import EHMX.HMX.NormalizationCompleteness

namespace EHMX.HMX.Constraints
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

/-- The existence property is separate from its algorithmic implementation.
Only the observed input names are compared; fresh output parameters are not
mistaken for additional inputs. No inference theorem is a field of this contract. -/
def PrincipalNormalForms (solved : X.Formula → Prop) : Prop :=
  ∀ (u : Names) (d : X.Formula), (X.freeNames d).Subset u →
    (∃ n : X.NormalForm, n.IsNormal solved d) →
    ∃ n : X.NormalForm, n.IsPrincipalOn u solved d

/-- Algebraic closure conditions are stated on equivalence to solved forms.
They are not silently inferred from scoped principality. Consistency is needed
for conjunction because every solved constraint must be satisfiable. -/
structure SolvedClosure (solved : X.Formula → Prop) : Prop where
  rename : ∀ (p : Renaming) c, X.Admissible solved c →
    X.Admissible solved (X.subst (p.asSubstitution T) c)
  conjoin : ∀ c d, X.Admissible solved c → X.Admissible solved d →
    X.Satisfiable (X.and c d) → X.Admissible solved (X.and c d)
  project : ∀ a c, X.Admissible solved c → X.Admissible solved (X.existsNames a c)

theorem SolvedClosure.satisfiable : X.SolvedClosure X.Satisfiable where
  rename := by
    intro p c hc
    exact (X.admissible_satisfiable_iff _).mpr ((X.satisfiable_rename_iff p c).mpr
      ((X.admissible_satisfiable_iff _).mp hc))
  conjoin := by
    intro c d _ _ sat
    exact (X.admissible_satisfiable_iff _).mpr sat
  project := by
    intro a c hc
    exact (X.admissible_satisfiable_iff _).mpr ((X.satisfiable_exists_iff a c).mpr
      ((X.admissible_satisfiable_iff _).mp hc))

/-- End-of-inference normalization starts with the identity substitution.
`none` means no normal form in the chosen representation, not necessarily an
inconsistent constraint. An executable instance must supply an executable map. -/
structure ScopedPrincipalNormalizer where
  solved : X.Formula → Prop
  solved_satisfiable : ∀ d, solved d → X.Satisfiable d
  normalize : Names → X.Formula → Option X.NormalForm
  principal : ∀ u d, (X.freeNames d).Subset u → ∀ n,
    normalize u d = some n → n.IsPrincipalOn u solved d
  failure : ∀ u d, (X.freeNames d).Subset u →
    (normalize u d = none ↔ ¬ ∃ n : X.NormalForm, n.IsNormal solved d)

namespace ScopedPrincipalNormalizer
variable {X}

theorem exists_of_normal (P : X.ScopedPrincipalNormalizer) {u : Names} {d : X.Formula}
    (scope : (X.freeNames d).Subset u)
    (normal : ∃ n : X.NormalForm, n.IsNormal P.solved d) :
    ∃ n, P.normalize u d = some n := by
  cases h : P.normalize u d with
  | none => exact False.elim ((P.failure u d scope).mp h normal)
  | some n => exact ⟨n, rfl⟩

theorem principalNormalForms (P : X.ScopedPrincipalNormalizer) :
    X.PrincipalNormalForms P.solved := by
  intro u d scope normal
  obtain ⟨n, hn⟩ := P.exists_of_normal scope normal
  exact ⟨n, P.principal u d scope n hn⟩

/-- Existence alone gives a classical model, not a decision procedure. -/
noncomputable def ofPrincipalNormalForms (solved : X.Formula → Prop)
    (sound : ∀ d, solved d → X.Satisfiable d)
    (principal : X.PrincipalNormalForms solved) : X.ScopedPrincipalNormalizer := by
  classical
  let run (u : Names) (d : X.Formula) : Option X.NormalForm :=
    if h : ∃ n : X.NormalForm, n.IsPrincipalOn u solved d then some h.choose else none
  refine ⟨solved, sound, run, ?_, ?_⟩
  · intro u d _ n hn
    dsimp [run] at hn
    split at hn
    · cases Option.some.inj hn
      exact Exists.choose_spec ‹∃ n : X.NormalForm, n.IsPrincipalOn u solved d›
    · contradiction
  · intro u d scope
    constructor
    · intro hn normal
      obtain ⟨n, hn'⟩ := principal u d scope normal
      simp [run, show ∃ n : X.NormalForm, n.IsPrincipalOn u solved d from ⟨n, hn'⟩] at hn
    · intro noNormal
      have noPrincipal : ¬ ∃ n : X.NormalForm, n.IsPrincipalOn u solved d :=
        fun ⟨n, hn⟩ => noNormal ⟨n, hn.1⟩
      simp [run, noPrincipal]

theorem sound (P : X.ScopedPrincipalNormalizer) {u : Names} {d : X.Formula}
    (scope : (X.freeNames d).Subset u) {n : X.NormalForm}
    (run : P.normalize u d = some n) :
    P.solved n.residual ∧ X.Satisfiable n.residual ∧
      X.Entails n.residual (X.subst n.substitution d) := by
  have normal := (P.principal u d scope n run).1
  exact ⟨normal.1, P.solved_satisfiable _ normal.1, NormalForm.reconstruct_entails X normal⟩

theorem failure_of_unsatisfiable (P : X.ScopedPrincipalNormalizer)
    {u : Names} {d : X.Formula} (scope : (X.freeNames d).Subset u)
    (unsat : ¬ X.Satisfiable d) : P.normalize u d = none := by
  apply (P.failure u d scope).mpr
  rintro ⟨n, hn⟩
  obtain ⟨v, hv⟩ := P.solved_satisfiable _ hn.1
  exact unsat ⟨n.substitution.pullback v,
    (X.holds_subst _ _ _).mp (NormalForm.reconstruct_entails X hn v hv)⟩

/-- A realizable competitor gives success and one uniform finite factor.
Unlike pointwise ground coverage, the factor works at every valuation. -/
theorem complete_of_competitor (P : X.ScopedPrincipalNormalizer)
    {u : Names} {d : X.Formula} (scope : (X.freeNames d).Subset u)
    (m : X.NormalForm) (hm : m.IsNormal P.solved d) :
    ∃ n, P.normalize u d = some n ∧ n.MoreGeneralOn u m := by
  obtain ⟨n, hn⟩ := P.exists_of_normal scope ⟨m, hm⟩
  exact ⟨n, hn, (P.principal u d scope n hn).2 m hm⟩

/-- Ground representability is an explicit additional premise of this
semantic corollary; it is not part of the normalizer interface. -/
theorem success_iff_satisfiable (P : X.ScopedPrincipalNormalizer)
    (Q : T.GroundRepresentation) {r : X.Formula} (hr : P.solved r)
    (hrTrue : ∀ v, X.holds r v) {u : Names} {d : X.Formula}
    (scope : (X.freeNames d).Subset u) :
    (∃ n, P.normalize u d = some n) ↔ X.Satisfiable d := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨_, ⟨v, hv⟩, he⟩ := P.sound scope hn
    exact ⟨n.substitution.pullback v, (X.holds_subst _ _ _).mp (he v hv)⟩
  · rintro ⟨v, hv⟩
    exact P.exists_of_normal scope
      ⟨NormalForm.groundOn X Q r d v, NormalForm.groundOn_isNormal X Q hr hrTrue v hv⟩

noncomputable def satisfiable (X : Constraints T O) : X.ScopedPrincipalNormalizer := by
 classical
 exact {
  solved := X.Satisfiable
  solved_satisfiable := fun _ h => h
  normalize := fun _ d => if X.Satisfiable d then some ⟨d, Substitution.identity T⟩ else none
  principal := by
    intro u d _ n run
    split at run
    · cases Option.some.inj run
      refine ⟨⟨‹X.Satisfiable d›, Substitution.identity_solved T, ?_, ?_⟩, ?_⟩
      · constructor <;> intro v hv <;>
          simpa only [X.holds_subst, Substitution.identity_pullback] using hv
      · exact X.entails_left _ _
      · intro m hm
        refine ⟨m.substitution, ?_⟩
        intro v hv
        refine ⟨?_, (X.holds_subst _ _ _).mp (Constraints.NormalForm.reconstruct_entails X hm v hv)⟩
        rw [Substitution.identity_pullback]
        exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    · contradiction
  failure := by
    intro u d _
    constructor
    · intro run ⟨n, hn⟩
      obtain ⟨v, hv⟩ := hn.1
      have sat : X.Satisfiable d := ⟨n.substitution.pullback v,
        (X.holds_subst _ _ _).mp (Constraints.NormalForm.reconstruct_entails X hn v hv)⟩
      simp [sat] at run
    · intro hn
      have noSat : ¬ X.Satisfiable d := by
        intro hd
        apply hn
        refine ⟨⟨d, Substitution.identity T⟩, hd, Substitution.identity_solved T, ⟨?_, ?_⟩,
          X.entails_left _ _⟩ <;> intro v hv <;>
          simpa only [X.holds_subst, Substitution.identity_pullback] using hv
      simp [noSat] }

end ScopedPrincipalNormalizer

end EHMX.HMX.Constraints
