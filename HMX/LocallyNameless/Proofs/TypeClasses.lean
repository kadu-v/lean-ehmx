import HMX.TypeClasses
import HMX.LocallyNameless.Proofs.InferenceTransfer

namespace HMX.TypeClasses.Proofs

theorem signatureValid (E : ClassEnv) : (signature E).Valid := by
  refine ⟨rfl, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · change 0 < 4 + E.extraArities.length; omega
  · intro f _
    simp only [signature, List.map_map, Function.comp_def]
    simpa using (List.nodup_range (n := arity E.extraArities f))
  · intro f _
    refine ⟨rfl, ?_⟩
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨Set.mem_univ _, rfl⟩
  · intro p _ k hk
    simpa [signature] using hk

theorem fixedModelRequirements (E : ClassEnv) : fixedModelRequirements E := by
  refine ⟨signatureValid E, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have : k = 0 := hk
    subst k
    exact ⟨Ground.int, rfl⟩
  · intros; rfl
  · intros; rfl
  · intro k _ a b c _ _ _ hab hbc; exact hab.trans hbc
  · intro k _ a b _ _ hab _; exact hab

theorem leMeaning (E : ClassEnv) (ρ : Assignment (model E)) (ι : GroundEnv (model E))
    (T U : Ty) :
    (Constraint.le 0 T U).Holds (signature E) (model E) ρ ι ↔
      T.eval (model E) ρ = U.eval (model E) ρ := by
  simp [Constraint.le, Constraint.Holds, Predicate.eval, model]

theorem fixedArrowLaw (E : ClassEnv) : fixedArrowLaw E := by
  intro T₁ T₂ U₁ U₂ _ _ _ _
  constructor <;> intro ρ ι _ _ h
  · have he := (leMeaning E ρ ι _ _).mp h
    simp only [Ty.arrow, Ty.eval, List.map_cons, List.map_nil, model, construct] at he
    obtain ⟨h₁,h₂⟩ := Ground.arrow.inj he
    exact ⟨(leMeaning E ρ ι _ _).mpr h₁.symm, (leMeaning E ρ ι _ _).mpr h₂⟩
  · apply (leMeaning E ρ ι _ _).mpr
    have h₁ := (leMeaning E ρ ι _ _).mp h.1
    have h₂ := (leMeaning E ρ ι _ _).mp h.2
    simp only [Ty.arrow, Ty.eval, List.map_cons, List.map_nil, model, construct]
    rw [h₁,h₂]

theorem constructTag (extras : List Nat) (f : Nat) (vs : List (Ground extras))
    (hf : f < 4 + extras.length) (hl : vs.length = arity extras f) :
    (construct extras f vs).tag = f := by
  rcases f with _ | _ | _ | _ | n
  · match vs with
    | [a,b] => rfl
    | [] | [_] | _ :: _ :: _ :: _ => simp [arity] at hl
  · have : vs = [] := List.eq_nil_of_length_eq_zero hl
    subst vs; rfl
  · have : vs = [] := List.eq_nil_of_length_eq_zero hl
    subst vs; rfl
  · match vs with
    | [a] => rfl
    | [] | _ :: _ :: _ => simp [arity] at hl
  · have hn : n < extras.length := by omega
    have hlen : vs.length = extras.get ⟨n,hn⟩ := by
      simpa [arity, List.getElem?_eq_getElem hn] using hl
    simp [construct, hn, hlen, Ground.tag]

/-- Valid applications preserve all arguments, including arbitrary extra arities. -/
theorem constructArguments (extras : List Nat) (f : Nat) (vs : List (Ground extras))
    (hf : f < 4 + extras.length) (hl : vs.length = arity extras f) :
    (construct extras f vs).arguments = vs := by
  rcases f with _ | _ | _ | _ | n
  · match vs with
    | [a,b] => rfl
    | [] | [_] | _ :: _ :: _ :: _ => simp [arity] at hl
  · have : vs = [] := List.eq_nil_of_length_eq_zero hl
    subst vs; rfl
  · have : vs = [] := List.eq_nil_of_length_eq_zero hl
    subst vs; rfl
  · match vs with
    | [a] => rfl
    | [] | _ :: _ :: _ => simp [arity] at hl
  · have hn : n < extras.length := by omega
    have hlen : vs.length = extras.get ⟨n,hn⟩ := by
      simpa [arity, List.getElem?_eq_getElem hn] using hl
    simp only [construct, dite_eq_left hn, dite_eq_left hlen, Ground.arguments]
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hlen.symm
    · intro i hi hj
      simp

theorem constructInjective (extras : List Nat) (f g : Nat) (vs us : List (Ground extras))
    (hf : f < 4 + extras.length) (hg : g < 4 + extras.length)
    (hv : vs.length = arity extras f) (hu : us.length = arity extras g)
    (h : construct extras f vs = construct extras g us) : f = g ∧ vs = us := by
  constructor
  · simpa only [constructTag extras f vs hf hv, constructTag extras g us hg hu]
      using congrArg Ground.tag h
  · simpa only [constructArguments extras f vs hf hv, constructArguments extras g us hg hu]
      using congrArg Ground.arguments h

theorem kindArity (E : ClassEnv) (f : Nat) (ts : List Ty) (k : Nat)
    (h : (Ty.con f ts).HasKind (signature E) k) :
    f < 4 + E.extraArities.length ∧ ts.length = arity E.extraArities f := by
  cases h with
  | con _ _ hf hts =>
    exact ⟨hf, by simpa [signature] using hts.length_eq⟩

theorem evalTag (E : ClassEnv) (ρ : Assignment (model E)) (f : Nat) (ts : List Ty)
    (h : (Ty.con f ts).HasKind (signature E) 0) :
    ((Ty.con f ts).eval (model E) ρ).tag = f := by
  obtain ⟨hf,hl⟩ := kindArity E f ts 0 h
  simp only [Ty.eval, model]
  exact constructTag _ _ (ts.map (Ty.eval (model E) ρ)) hf (by simpa using hl)

theorem fixedIsolation (E : ClassEnv) : fixedIsolation E := by
  refine ⟨?_, fun _ h => h, ?_⟩
  · change 0 < 4 + E.extraArities.length; omega
  · intro f _ g _ hfg _ ts us hts hus
    have hne (ρ : Assignment (model E)) :
        (Ty.con f ts).eval (model E) ρ ≠ (Ty.con g us).eval (model E) ρ := by
      intro he
      have := congrArg Ground.tag he
      rw [evalTag E ρ f ts hts, evalTag E ρ g us hus] at this
      exact hfg this
    constructor <;> constructor <;> intro ρ ι _ _ h
    · exact hne ρ ((leMeaning E ρ ι _ _).mp h)
    · exact h.elim
    · exact hne ρ ((leMeaning E ρ ι _ _).mp h).symm
    · exact h.elim

theorem fixedFramework (E : ClassEnv) : fixedFramework E :=
  ⟨fixedModelRequirements E, fixedArrowLaw E, fixedIsolation E⟩

theorem classAtomMeaning (E : ClassEnv) : classAtomMeaning E := by
  intro c T ρ ι
  simp [classAtom, Constraint.Holds, Predicate.eval, model]

theorem superclassEntailment (E : ClassEnv) : superclassEntailment E := by
  intro c d h T ρ ι _ _ hc
  exact (classAtomMeaning E d T ρ ι).mpr
    (.superclass c d _ h ((classAtomMeaning E c T ρ ι).mp hc))

theorem instanceContextMeaning (E : ClassEnv) (r : InstanceRule) (ts : List Ty)
    (ρ : Assignment (model E)) (ι : GroundEnv (model E)) :
    (instanceContext r ts).Holds (signature E) (model E) ρ ι ↔
    ∀ p ∈ r.premises, Member E p.1 (((ts[p.2]?).getD (.con 1 [])).eval (model E) ρ) := by
  unfold instanceContext
  induction r.premises with
  | nil => simp [Constraint.Holds]
  | cons p ps ih =>
    simp only [List.map_cons, List.foldr_cons, Constraint.Holds, List.mem_cons,
      forall_eq_or_imp, classAtomMeaning E p.1 _ ρ ι, ih]

theorem instanceEntailment (E : ClassEnv) : instanceEntailment E := by
  intro hE r hr ts hl ρ ι _ _ hc
  apply (classAtomMeaning E _ _ ρ ι).mpr
  simp only [Ty.eval, model]
  apply Member.instanceRule r (ts.map (Ty.eval (model E) ρ)) hr (by simpa using hl)
  intro p hp
  have hi : p.2 < ts.length := by rw [hl]; exact (hE.2 r hr).2.2 p hp |>.2
  have hh := (instanceContextMeaning E r ts ρ ι).mp hc p hp
  simpa [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by simpa using hi),
    List.getElem_map] using hh

theorem memberDeclared (E : ClassEnv) (hE : E.WF) (c : Nat) (v : Ground E.extraArities)
    (h : Member E c v) : c ∈ E.classes := by
  induction h with
  | instanceRule r vs hr _ _ => exact (hE.2 r hr).1
  | superclass c d v hr _ _ => exact (hE.1 (c,d) hr).2

/-- Application of ATTAPL 10.4.4 Soundness; Framework is constructed here. -/
theorem theorem10_4_4_soundness_scoped (E : ClassEnv) : namedSoundness E :=
  HMX.Proofs.theorem10_4_4_soundness_scoped _ _ _ (fixedFramework E)

/-- Application of ATTAPL 10.4.8 Completeness, with its feasibility premise intact. -/
theorem theorem10_4_8_completeness (E : ClassEnv) : namedCompleteness E :=
  HMX.Proofs.theorem10_4_8_completeness _ _ _ (fixedFramework E)

theorem constraintGenerationPrincipality_scoped (E : ClassEnv) : namedPrincipality E :=
  HMX.Proofs.constraintGenerationPrincipality_scoped _ _ _ (fixedFramework E)

end HMX.TypeClasses.Proofs
