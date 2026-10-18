import EHMX.TypeClasses
import EHMX.Proofs.InferencePrincipality
import HMX.LocallyNameless.Proofs.TypeClasses
import Mathlib.Data.Set.Finite.Basic

namespace EHMX.TypeClasses

theorem groundRefl (T : GroundType extras) : T.Below T := by
  induction T with
  | int => exact .int
  | bool => exact .bool
  | list a _ => exact .list a
  | extra i args _ => exact .extra i args
  | arrow a ε b ihA ihB => exact .arrow ihA (fun _ h => h) ihB

theorem groundTrans (h : GroundType.Below a b) (h' : GroundType.Below b c) :
    GroundType.Below a c := by
  induction b generalizing a c with
  | int => cases h; cases h'; exact .int
  | bool => cases h; cases h'; exact .bool
  | list a _ => cases h; cases h'; exact .list a
  | extra i args _ => cases h; cases h'; exact .extra i args
  | arrow a ε b ihA ihB =>
      cases h with
      | arrow ha hε hb =>
          cases h' with
          | arrow ha' hε' hb' =>
              exact .arrow (ihA ha' ha) (fun _ h => hε' (hε h)) (ihB hb hb')

theorem groundAntisymm (h : GroundType.Below a b) (h' : GroundType.Below b a) : a = b := by
  induction b generalizing a with
  | int => cases h; rfl
  | bool => cases h; rfl
  | list a _ => cases h; rfl
  | extra i args _ => cases h; rfl
  | arrow a ε b ihA ihB =>
      cases h with
      | arrow ha hε hb =>
          cases h' with
          | arrow ha' hε' hb' =>
              have hA := ihA ha' ha
              have hB := ihB hb hb'
              have hE := Finset.Subset.antisymm hε hε'
              subst_vars
              rfl

theorem kindZero (h : kind a = 0) : ∃ T, a = .type T := by
  cases a with
  | type T => exact ⟨T, rfl⟩
  | effect ε => simp [kind] at h

theorem kindOne (h : kind a = 1) : ∃ ε, a = .effect ε := by
  cases a with
  | type T => simp [kind] at h
  | effect ε => exact ⟨ε, rfl⟩

theorem constructorKind (E : ClassEnv) (f : Symbol) {vs : List (Ground E.extraArities)}
    (h : KindValues (model E) (f.parameters (signature E)) vs) :
    kind (constructor E.extraArities f vs) = f.result (signature E) := by
  cases f with
  | empty => cases h; rfl
  | operation op => cases h; rfl
  | other n => cases n <;> rfl
  | arrow =>
      cases h with
      | cons ha h =>
          cases h with
          | cons hε h =>
              cases h with
              | cons hb h =>
                  cases h
                  obtain ⟨a, rfl⟩ := kindZero ha
                  obtain ⟨ε, rfl⟩ := kindOne hε
                  obtain ⟨b, rfl⟩ := kindZero hb
                  rfl
  | union =>
      cases h with
      | cons hε h =>
          cases h with
          | cons hη h =>
              cases h
              obtain ⟨ε, rfl⟩ := kindOne hε
              obtain ⟨η, rfl⟩ := kindOne hη
              rfl

theorem fixedFramework (E : ClassEnv) : EffectFramework (signature E) (model E) where
  signature := by
    refine ⟨by simp [signature], by simp [signature], ?_, ?_⟩
    · intro f hf; constructor
      · simp [signature]
      · intro k hk; simp only [signature, List.mem_replicate] at hk; simp [signature, hk.2]
    · intro p hp k hk
      have : k = 0 := by simpa [signature] using hk
      simp [signature, this]
  inhabited := by
    intro k hk
    rcases (show k = 0 ∨ k = 1 from hk) with rfl | rfl
    · exact ⟨.type .int, rfl⟩
    · exact ⟨.effect ∅, rfl⟩
  constructorKind := fun f _ _ h => constructorKind E f h
  belowRefl := by
    intro k _ a ha
    cases a with
    | type T => cases ha; exact groundRefl T
    | effect ε => cases ha; exact fun _ h => h
  belowTrans := by
    intro k _ a b c ha hb hc hab hbc
    cases a with
    | type T =>
        cases ha
        obtain ⟨U, rfl⟩ := kindZero hb
        obtain ⟨V, rfl⟩ := kindZero hc
        exact groundTrans hab hbc
    | effect ε =>
        cases ha
        obtain ⟨η, rfl⟩ := kindOne hb
        obtain ⟨ζ, rfl⟩ := kindOne hc
        exact fun _ h => hbc (hab h)
  belowAntisymm := by
    intro k _ a b ha hb hab hba
    cases a with
    | type T =>
        cases ha
        obtain ⟨U, rfl⟩ := kindZero hb
        exact congrArg Ground.type (groundAntisymm hab hba)
    | effect ε =>
        cases ha
        obtain ⟨η, rfl⟩ := kindOne hb
        exact congrArg Ground.effect (Finset.Subset.antisymm hab hba)
  effectOrder := by
    intro a b ha hb
    obtain ⟨ε, rfl⟩ := kindOne ha
    obtain ⟨η, rfl⟩ := kindOne hb
    rfl
  emptyEffect := by ext; simp [constructor, effects]
  effectsFinite := by
    intro a ha
    obtain ⟨ε, rfl⟩ := kindOne ha
    exact ε.finite_toSet
  singletonEffect := fun _ => by ext; simp [constructor, effects]
  unionEffect := by
    intro a b ha hb
    obtain ⟨ε, rfl⟩ := kindOne ha
    obtain ⟨η, rfl⟩ := kindOne hb
    ext; simp [constructor, effects]
  arrowOrder := by
    intro a ε b a' ε' b' ha hε hb ha' hε' hb'
    obtain ⟨A, rfl⟩ := kindZero ha
    obtain ⟨E, rfl⟩ := kindOne hε
    obtain ⟨B, rfl⟩ := kindZero hb
    obtain ⟨A', rfl⟩ := kindZero ha'
    obtain ⟨E', rfl⟩ := kindOne hε'
    obtain ⟨B', rfl⟩ := kindZero hb'
    constructor
    · intro h; cases h with | arrow ha he hb => exact ⟨ha,he,hb⟩
    · rintro ⟨ha,he,hb⟩; exact .arrow ha he hb


theorem constructTag (extras : List Nat) (ε : Finset Op) (f : Nat) (vs : List (GroundType extras))
    (hf : f < 4 + extras.length) (hl : vs.length = arity extras f) :
    (construct extras ε f vs).tag = f := by
  rcases f with _ | _ | _ | _ | n
  · match vs with
    | [a,b] => rfl
    | [] | [_] | _ :: _ :: _ :: _ => simp [arity, HMX.TypeClasses.arity] at hl
  · have : vs = [] := List.eq_nil_of_length_eq_zero hl
    subst vs; rfl
  · have : vs = [] := List.eq_nil_of_length_eq_zero hl
    subst vs; rfl
  · match vs with
    | [a] => rfl
    | [] | _ :: _ :: _ => simp [arity, HMX.TypeClasses.arity] at hl
  · have hn : n < extras.length := by omega
    have hlen : vs.length = extras.get ⟨n,hn⟩ := by
      simpa [arity, HMX.TypeClasses.arity, List.getElem?_eq_getElem hn] using hl
    simp [construct, hn, hlen, GroundType.tag]

/-- Valid applications preserve all arguments, including arbitrary extra arities. -/
theorem constructArguments (extras : List Nat) (ε : Finset Op) (f : Nat) (vs : List (GroundType extras))
    (hf : f < 4 + extras.length) (hl : vs.length = arity extras f) :
    (construct extras ε f vs).arguments = vs := by
  rcases f with _ | _ | _ | _ | n
  · match vs with
    | [a,b] => rfl
    | [] | [_] | _ :: _ :: _ :: _ => simp [arity, HMX.TypeClasses.arity] at hl
  · have : vs = [] := List.eq_nil_of_length_eq_zero hl
    subst vs; rfl
  · have : vs = [] := List.eq_nil_of_length_eq_zero hl
    subst vs; rfl
  · match vs with
    | [a] => rfl
    | [] | _ :: _ :: _ => simp [arity, HMX.TypeClasses.arity] at hl
  · have hn : n < extras.length := by omega
    have hlen : vs.length = extras.get ⟨n,hn⟩ := by
      simpa [arity, HMX.TypeClasses.arity, List.getElem?_eq_getElem hn] using hl
    simp only [construct, dite_eq_left hn, dite_eq_left hlen, GroundType.arguments]
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hlen.symm
    · intro i hi hj
      simp


theorem fixedArrowSeparated (E : ClassEnv) : ArrowSeparated (signature E) (model E) := by
  intro f hf _ vs a ε b hv ha hε hb h
  obtain ⟨A, rfl⟩ := kindZero ha
  obtain ⟨F, rfl⟩ := kindOne hε
  obtain ⟨B, rfl⟩ := kindZero hb
  have ht := constructTag E.extraArities ∅ f (vs.map Ground.asType) hf.2
    (by simpa [signature] using hv.length_eq)
  cases f with
  | zero => exact (Nat.lt_irrefl 0 hf.1)
  | succ f =>
    change GroundType.Below (if vs.all (fun v => kind v == 0) then
      construct E.extraArities ∅ (f+1) (vs.map Ground.asType) else .int) (.arrow A F B) at h
    split at h
    · have he : (construct E.extraArities ∅ (f+1) (vs.map Ground.asType)).tag = 0 := by
        generalize construct E.extraArities ∅ (f+1) (vs.map Ground.asType) = t at h ⊢
        cases h
        rfl
      omega
    · cases h

theorem classAtomMeaning (E : ClassEnv) (c : Nat) (T : Ty) (ρ : Assignment (model E)) bs ι :
    (classAtom c T).Holds (model E) ρ bs ι ↔
      ∃ v, T.eval (model E) ρ bs = .type v ∧ Member E c v := by
  simp [classAtom, Constraint.Holds, Predicate.eval]

theorem superclassEntailment (E : ClassEnv) (c d : Nat) (h : (c,d) ∈ E.supers) (T : Ty) :
    Entails (signature E) (model E) Δ (classAtom c T) (classAtom d T) := by
  intro ρ bs ι _ _ _ hc
  obtain ⟨v, hv, hm⟩ := (classAtomMeaning E c T ρ bs ι).mp hc
  exact (classAtomMeaning E d T ρ bs ι).mpr ⟨v, hv, .superclass c d v h hm⟩

theorem memberDeclared (E : ClassEnv) (hE : E.WF) {c : Nat} {v : GroundType E.extraArities} (h : Member E c v) : c ∈ E.classes := by
  induction h with
  | instanceRule r vs ε hr _ _ => exact (hE.2 r hr).1
  | superclass c d v hr _ _ => exact (hE.1 (c,d) hr).2

/-- ATTAPL 10.4.4 extended with effects; the model laws are discharged internally. -/
theorem inferenceSoundness (E : ClassEnv) (sig : OpSignature) (hSig : sig.WF (signature E))
    (Δ Γ e T ε) (hΔ : ∀ k ∈ Δ, k ∈ (signature E).kinds)
    (hΓ : Γ.WF (signature E) Δ) (he : e.Scoped Γ) (hd : e.Declared sig)
    (hT : T.HasKind (signature E) Δ 0) (hε : ε.HasKind (signature E) Δ 1) :
    Typing (signature E) (model E) sig Δ (infer sig Γ e T ε) Γ e T ε :=
  EHMX.inferenceSoundness _ _ _ ⟨fixedFramework E, hSig⟩ Δ Γ e T ε hΔ hΓ he hd hT hε

/-- ATTAPL 10.4.8 extended with effects, retaining environment feasibility. -/
theorem inferenceCompleteness (E : ClassEnv) (sig : OpSignature) (hSig : sig.WF (signature E))
    (Δ C Γ e T ε) (hΔ : ∀ k ∈ Δ, k ∈ (signature E).kinds)
    (hΓe : Entails (signature E) (model E) Δ C Γ.exists_)
    (ht : Typing (signature E) (model E) sig Δ C Γ e T ε) :
    Entails (signature E) (model E) Δ C (infer sig Γ e T ε) :=
  EHMX.inferenceCompleteness _ _ _ ⟨fixedFramework E, hSig⟩ Δ C Γ e T ε hΔ hΓe ht

/-- ATTAPL pp.429–430 extended with effects: a principal constraint, not a solver. -/
theorem constraintGenerationPrincipality (E : ClassEnv) (sig : OpSignature) (hSig : sig.WF (signature E))
    (Δ Γ e T ε) (hΔ : ∀ k ∈ Δ, k ∈ (signature E).kinds)
    (hΓ : Γ.WF (signature E) Δ) (he : e.Scoped Γ) (hd : e.Declared sig)
    (hT : T.HasKind (signature E) Δ 0) (hε : ε.HasKind (signature E) Δ 1) :
    PrincipalConstraint (signature E) (model E) sig Δ Γ e T ε (infer sig Γ e T ε) :=
  EHMX.constraintGenerationPrincipality _ _ _ ⟨fixedFramework E, hSig⟩ Δ Γ e T ε hΔ hΓ he hd hT hε


@[simp] theorem eraseEmbed (v : HMX.TypeClasses.Ground extras) : erase (embed v) = v := by
  induction v with
  | int | bool => rfl
  | arrow a b ha hb => simp [embed, erase, ha, hb]
  | list a ha => simp [embed, erase, ha]
  | extra i args ih => simp [embed, erase, ih]

theorem embedConstruct (extras : List Nat) (f : Nat) (vs : List (HMX.TypeClasses.Ground extras)) :
    embed (HMX.TypeClasses.construct extras f vs) = construct extras ∅ f (vs.map embed) := by
  rcases f with _ | _ | _ | _ | n
  all_goals try (cases vs with
    | nil => rfl
    | cons a vs => cases vs with
      | nil => rfl
      | cons b vs => cases vs <;> rfl)
  by_cases hn : n < extras.length
  · by_cases hl : vs.length = extras[n]
    · simp [HMX.TypeClasses.construct, construct, hn, hl, embed, List.get_eq_getElem]
    · simp [HMX.TypeClasses.construct, construct, hn, hl, embed]
  · simp [HMX.TypeClasses.construct, construct, hn, embed]

theorem eraseConstruct (extras : List Nat) (ε : Finset Op) (f : Nat) (vs : List (GroundType extras)) :
    erase (construct extras ε f vs) = HMX.TypeClasses.construct extras f (vs.map erase) := by
  rcases f with _ | _ | _ | _ | n
  all_goals try (cases vs with
    | nil => rfl
    | cons a vs => cases vs with
      | nil => rfl
      | cons b vs => cases vs <;> rfl)
  by_cases hn : n < extras.length
  · by_cases hl : vs.length = extras[n]
    · simp [HMX.TypeClasses.construct, construct, hn, hl, erase, List.get_eq_getElem]
    · simp [HMX.TypeClasses.construct, construct, hn, hl, erase]
  · simp [HMX.TypeClasses.construct, construct, hn, erase]

theorem memberEmbed {E : ClassEnv} {c : Nat} {v : HMX.TypeClasses.Ground E.extraArities}
    (h : HMX.TypeClasses.Member E c v) : Member E c (embed v) := by
  induction h with
  | instanceRule r vs hr hl hp ih =>
    rw [embedConstruct]
    apply Member.instanceRule r (vs.map embed) ∅ hr (by simpa using hl)
    intro p hp
    simp only [List.getElem?_map]
    cases ho : vs[p.2]? <;> simpa [ho, embed] using ih p hp
  | superclass c d v hr h ih => exact .superclass c d _ hr ih

theorem memberErase {E : ClassEnv} {c : Nat} {v : GroundType E.extraArities}
    (h : Member E c v) : HMX.TypeClasses.Member E c (erase v) := by
  induction h with
  | instanceRule r vs ε hr hl hp ih =>
    rw [eraseConstruct]
    apply HMX.TypeClasses.Member.instanceRule r (vs.map erase) hr (by simpa using hl)
    intro p hp
    simp only [List.getElem?_map]
    cases ho : vs[p.2]? <;> simpa [ho, erase] using ih p hp
  | superclass c d v hr h ih => exact .superclass c d _ hr ih

/-- Only class membership is compared, not the two inference systems. -/
theorem memberEmbedIff (E : ClassEnv) (c : Nat) (v : HMX.TypeClasses.Ground E.extraArities) :
    Member E c (embed v) ↔ HMX.TypeClasses.Member E c v :=
  ⟨fun h => by simpa using memberErase h, memberEmbed⟩


theorem instanceContextMeaning (E : ClassEnv) (r : InstanceRule) (ts : List Ty)
    (ρ : Assignment (model E)) bs ι :
    (instanceContext r ts).Holds (model E) ρ bs ι ↔
    ∀ p ∈ r.premises, ∃ v,
      ((ts[p.2]?).getD (.con (.other 1) [])).eval (model E) ρ bs = .type v ∧ Member E p.1 v := by
  unfold instanceContext
  induction r.premises with
  | nil => simp [Constraint.Holds]
  | cons p ps ih =>
    simp only [List.map_cons, List.foldr_cons, Constraint.Holds, List.mem_cons,
      forall_eq_or_imp, classAtomMeaning, ih]

theorem instanceHeadEval (E : ClassEnv) (r : InstanceRule) (ts : List Ty) (ε : Effect)
    (hargs : ∀ T ∈ ts, T.HasKind (signature E) Δ 0)
    (hl : ts.length = arity E.extraArities r.constructor)
    (ρ : Assignment (model E)) bs (hρ : ρ.Valid (signature E) (model E))
    (hbs : KindValues (model E) Δ bs) (F : Finset Op)
    (hF : ε.eval (model E) ρ bs = .effect F) :
    (instanceHead r ts ε).eval (model E) ρ bs = .type
      (construct E.extraArities F r.constructor (ts.map (fun T => (T.eval (model E) ρ bs).asType))) := by
  rcases r with ⟨c, f, ps⟩
  cases f with
  | zero =>
    have hlen : ts.length = 2 := hl
    match ts with
    | [a,b] =>
      obtain ⟨A, hA⟩ := kindZero (evalKind (fixedFramework E) hρ hbs (hargs a (by simp)))
      obtain ⟨B, hB⟩ := kindZero (evalKind (fixedFramework E) hρ hbs (hargs b (by simp)))
      simp [instanceHead, Ty.arrow, Ty.eval, hA, hB, hF, constructor, construct, Ground.asType]
    | [] | [_] | _ :: _ :: _ :: _ => simp at hlen
  | succ f =>
    have hall : (ts.map (Ty.eval (model E) ρ bs)).all (fun v => kind v == 0) = true := by
      apply List.all_eq_true.mpr
      intro v hv
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hv
      exact beq_iff_eq.mpr (evalKind (fixedFramework E) hρ hbs (hargs T hT))
    simp only [instanceHead, Nat.succ_ne_zero, ↓reduceIte, Ty.eval, constructor, hall, List.map_map]
    congr 1
    rcases f with _ | _ | _ | n
    all_goals first | rfl | (cases ts with
      | nil => rfl
      | cons a ts => cases ts <;> rfl)

theorem instanceEntailment (E : ClassEnv) (hE : E.WF) (r : InstanceRule) (hr : r ∈ E.instances)
    (ts : List Ty) (hl : ts.length = arity E.extraArities r.constructor)
    (hargs : ∀ T ∈ ts, T.HasKind (signature E) Δ 0)
    (ε : Effect) (hε : ε.HasKind (signature E) Δ 1) :
    Entails (signature E) (model E) Δ (instanceContext r ts)
      (classAtom r.className (instanceHead r ts ε)) := by
  intro ρ bs ι hρ hbs _ hc
  obtain ⟨F, hF⟩ := kindOne (evalKind (fixedFramework E) hρ hbs hε)
  apply (classAtomMeaning E _ _ ρ bs ι).mpr
  refine ⟨_, instanceHeadEval E r ts ε hargs hl ρ bs hρ hbs F hF, ?_⟩
  apply Member.instanceRule r _ F hr (by simpa using hl)
  intro p hp
  have hi : p.2 < ts.length := by rw [hl]; exact (hE.2 r hr).2.2 p hp |>.2
  obtain ⟨v, hv, hm⟩ := (instanceContextMeaning E r ts ρ bs ι).mp hc p hp
  simp only [List.getElem?_eq_getElem hi, Option.getD_some] at hv
  simpa [List.getElem?_eq_getElem (by simpa using hi), hv, Ground.asType] using hm


/-- Kind-correct ordinary applications preserve every child, including nested effects. -/
theorem constructorTypes (extras : List Nat) (f : Nat) (hf : f ≠ 0) (vs : List (GroundType extras)) :
    constructor extras (.other f) (vs.map Ground.type) = .type (construct extras ∅ f vs) := by
  cases f with
  | zero => exact (hf rfl).elim
  | succ f => simp [constructor, List.map_map, Function.comp_def, kind, Ground.asType]

theorem constructorPreserves (E : ClassEnv) (f : Nat) (hf : f ∈ (signature E).constructors)
    (vs : List (GroundType E.extraArities)) (hl : vs.length = arity E.extraArities f) :
    ∃ v, constructor E.extraArities (.other f) (vs.map Ground.type) = .type v ∧
      v.tag = f ∧ v.arguments = vs :=
  ⟨_, constructorTypes _ _ (Nat.ne_of_gt hf.1) _,
    constructTag _ _ _ _ hf.2 hl, constructArguments _ _ _ _ hf.2 hl⟩

end EHMX.TypeClasses
