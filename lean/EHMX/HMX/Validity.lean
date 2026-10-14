import EHMX.HMX.Inference
import EHMX.HMX.SemanticSupport

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

namespace Constraints
variable (X : Constraints T O)

theorem satisfiable_of_entails {c d : X.Formula}
    (h : X.Entails c d) (hc : X.Satisfiable c) : X.Satisfiable d := by
  obtain ⟨v, hv⟩ := hc
  exact ⟨v, h v hv⟩

theorem admissible_satisfiable_iff (c : X.Formula) :
    X.Admissible X.Satisfiable c ↔ X.Satisfiable c := by
  constructor
  · rintro ⟨d, hd, he⟩
    exact X.satisfiable_of_entails he.2 hd
  · intro hc
    exact ⟨c, hc, X.entails_refl c, X.entails_refl c⟩

theorem satisfiable_exists_iff (a : Names) (c : X.Formula) :
    X.Satisfiable (X.existsNames a c) ↔ X.Satisfiable c := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, _, hw⟩ := (X.holds_exists a c v).mp hv
    exact ⟨w, hw⟩
  · exact X.satisfiable_of_entails (X.exists_intro a c)

theorem satisfiable_subst (s : Substitution T) (c : X.Formula)
    (h : X.Satisfiable (X.subst s c)) : X.Satisfiable c := by
  obtain ⟨v, hv⟩ := h
  exact ⟨s.pullback v, (X.holds_subst s c v).mp hv⟩

theorem satisfiable_clause (a b : Names) (c : X.Formula)
    (h : X.Satisfiable (X.clause a b c)) : X.Satisfiable c := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨w, _, hw⟩ := (X.holds_clause a b c v).mp hv v
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  exact ⟨w, hw⟩

end Constraints

theorem Constraints.satisfiable_rename_iff (X : Constraints T O)
    (p : Renaming) (c : X.Formula) :
    X.Satisfiable (X.subst (p.asSubstitution T) c) ↔ X.Satisfiable c := by
  refine ⟨X.satisfiable_subst _ _, ?_⟩
  rintro ⟨v, hv⟩
  refine ⟨⟨v.types ∘ p.types.symm, v.effects ∘ p.effects.symm⟩, ?_⟩
  apply (X.holds_subst _ _ _).mpr
  simpa only [p.pullback_inverse] using hv

theorem Scheme.AlphaEquivalent.admissible_iff {X : Constraints T O}
    {s t : Scheme X} (h : Scheme.AlphaEquivalent X s t) :
    s.Admissible X.Satisfiable ↔ t.Admissible X.Satisfiable := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | rename p _ _ =>
      simp only [Scheme.Admissible, X.admissible_satisfiable_iff]
      exact (X.satisfiable_rename_iff p _).symm

/-- Alpha admissibility for an arbitrary solved set requires transport of
admissibility under finite permutations. This is a hypothesis on that set,
not a consequence of scoped normal-form comparison. -/
theorem Scheme.AlphaEquivalent.admissible_of_rename {X : Constraints T O}
    {solved : X.Formula → Prop}
    (rename : ∀ (p : Renaming) c, X.Admissible solved c →
      X.Admissible solved (X.subst (p.asSubstitution T) c))
    {s t : Scheme X} (h : Scheme.AlphaEquivalent X s t) :
    s.Admissible solved ↔ t.Admissible solved := by
  have equivalent {c d : X.Formula} (hc : X.Admissible solved c)
      (he : X.Equivalent c d) : X.Admissible solved d := by
    obtain ⟨r, hr, forward, backward⟩ := hc
    exact ⟨r, hr, X.entails_trans he.2 forward, X.entails_trans backward he.1⟩
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @rename p a c t _ _ =>
      change X.Admissible solved c ↔ X.Admissible solved (X.subst (p.asSubstitution T) c)
      refine ⟨rename p c, fun hc => equivalent (rename p.inverse _ hc) ?_⟩
      have inverse (v : Valuation T.Value) :
          (p.asSubstitution T).pullback ((p.inverse.asSubstitution T).pullback v) = v := by
        cases v
        simp [Substitution.pullback, Renaming.asSubstitution, Renaming.inverse,
          T.eval_var, Effect.eval, Effect.var]
      constructor <;> intro v hv <;>
        simpa only [X.holds_subst, inverse] using hv

theorem Context.admissible_cons {X : Constraints T O} {solved : X.Formula → Prop}
    {g : Context X} {s : Scheme X} (hg : g.Admissible solved)
    (hs : s.Admissible solved) : Context.Admissible (s :: g) solved := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hs
  · exact hg t ht

theorem Derivation.Valid.result {sig : Signature T} {X : Constraints T O}
    {solved : X.Formula → Prop} {c g e s eff}
    {tree : Derivation sig X c g e s eff} (h : tree.Valid solved) : s.Admissible solved := by
  cases tree <;> exact h.2.2.1

/-- In the constraint-based fragment, a satisfiable root and admissible
environment make every node of a declarative derivation valid. In particular,
existential generalization and rigid handler clauses do not hide an
unsatisfiable child constraint. -/
theorem Derivation.valid_of_satisfiable {sig : Signature T} {X : Constraints T O}
    {c g e s eff} (tree : Derivation sig X c g e s eff)
    (hc : X.Satisfiable c) (hg : g.Admissible X.Satisfiable) :
    tree.Valid X.Satisfiable := by
  induction tree with
  | var found =>
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg,
        hg _ (List.mem_of_getElem? found), trivial⟩
  | int n => exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial, trivial⟩
  | bool b => exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial, trivial⟩
  | lam body ih =>
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial,
        ih hc (Context.admissible_cons hg trivial)⟩
  | app f x ihf ihx =>
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial, ihf hc hg, ihx hc hg⟩
  | letVal hv v b ihv ihb =>
      have hval := ihv hc hg
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial, hval,
        ihb hc (Context.admissible_cons hg (Derivation.Valid.result hval))⟩
  | letMono hv v b ihv ihb =>
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial, ihv hc hg,
        ihb hc (Context.admissible_cons hg trivial)⟩
  | sub body he ih =>
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial, ih hc hg⟩
  | @forallIntro c d g e a t hv ha fresh body ih =>
      have hp := X.satisfiable_of_entails (X.entails_right _ _) hc
      have hd := (X.satisfiable_exists_iff a d).mp hp
      have hcd := (X.satisfiable_exists_iff a (X.and c d)).mp
        (X.satisfiable_of_entails (X.project_and_avoids ha).2 hc)
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg,
        (X.admissible_satisfiable_iff _).mpr hd, ih hcd hg⟩
  | forallElim s ht he body hd ih =>
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial, ih hc hg⟩
  | existsIntro hga hsa hea body ih =>
      have hi := ih ((X.satisfiable_exists_iff _ _).mp hc) hg
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, Derivation.Valid.result hi, hi⟩
  | weaken body he ih =>
      have hi := ih (X.satisfiable_of_entails he hc) hg
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, Derivation.Valid.result hi, hi⟩
  | effectEq body he ih =>
      have hi := ih hc hg
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, Derivation.Valid.result hi, hi⟩
  | alpha body he ih =>
      have hi := ih hc hg
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg,
        he.admissible_iff.mp (Derivation.Valid.result hi), hi⟩
  | perform s hs hclosed ht he body ih =>
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial, ih hc hg⟩
  | handle hs hclosed fresh hga htypes heffects hw hwc hwe body ret clause hh hsplit hr her
      ihb ihr ihc =>
      have hclause := X.satisfiable_of_entails (X.entails_left _ _)
        (X.satisfiable_clause _ _ _ (X.satisfiable_of_entails hh hc))
      exact ⟨(X.admissible_satisfiable_iff _).mpr hc, hg, trivial,
        ihb hc hg, ihr hc (Context.admissible_cons hg trivial),
        ihc hclause (Context.admissible_cons (Context.admissible_cons hg trivial) trivial)⟩

namespace Typing
variable {sig : Signature T} {X : Constraints T O} {solved : X.Formula → Prop}

theorem root {c g e s eff} (h : Typing sig X solved c g e s eff) :
    X.Admissible solved c ∧ g.Admissible solved ∧ s.Admissible solved := by
  obtain ⟨tree, ht⟩ := h
  cases tree <;> exact ⟨ht.1, ht.2.1, ht.2.2.1⟩

/-- Every valid solved-form derivation is also valid in the constraint-based
system. The same tree is retained, including its internal qualifiers. -/
theorem to_satisfiable {c g e s eff} (h : Typing sig X solved c g e s eff)
    (sound : ∀ d, solved d → X.Satisfiable d) :
    Typing sig X X.Satisfiable c g e s eff := by
  have admissible {d : X.Formula} (hd : X.Admissible solved d) :
      X.Admissible X.Satisfiable d := by
    obtain ⟨r, hr, equivalent⟩ := hd
    exact ⟨r, sound r hr, equivalent⟩
  have root := h.root
  obtain ⟨tree, _⟩ := h
  refine ⟨tree, tree.valid_of_satisfiable
    ((X.admissible_satisfiable_iff c).mp (admissible root.1)) ?_⟩
  intro s hs
  cases s with
  | mono => trivial
  | qualified => exact admissible (root.2.1 _ hs)

theorem weaken {c d g e s eff} (h : Typing sig X solved c g e s eff)
    (hd : X.Admissible solved d) (he : X.Entails d c) :
    Typing sig X solved d g e s eff := by
  have hr := h.root
  obtain ⟨tree, ht⟩ := h
  exact ⟨.weaken tree he, hd, hr.2.1, hr.2.2, ht⟩

theorem sub {c g e a b eff} (h : Typing sig X solved c g e (.mono a) eff)
    (he : X.Entails c (X.le a b)) : Typing sig X solved c g e (.mono b) eff := by
  have hr := h.root
  obtain ⟨tree, ht⟩ := h
  exact ⟨.sub tree he, hr.1, hr.2.1, trivial, ht⟩

theorem forallElim {c d g e a t eff}
    (h : Typing sig X solved c g e (.qualified a d t) eff)
    (σ : Substitution T) (ht : σ.domain.types ⊆ a.types)
    (he : σ.domain.effects ⊆ a.effects) (hd : X.Entails c (X.subst σ d)) :
    Typing sig X solved c g e (.mono (σ.apply t)) eff := by
  have hr := h.root
  obtain ⟨tree, valid⟩ := h
  exact ⟨.forallElim σ ht he tree hd, hr.1, hr.2.1, trivial, valid⟩

theorem alpha {c g e s s' eff} (h : Typing sig X solved c g e s eff)
    (he : Scheme.AlphaEquivalent X s s') (hs : s'.Admissible solved) :
    Typing sig X solved c g e s' eff := by
  have hr := h.root
  obtain ⟨tree, valid⟩ := h
  exact ⟨.alpha tree he, hr.1, hr.2.1, hs, valid⟩

theorem effectEq {c g e s eff eff'} (h : Typing sig X solved c g e s eff)
    (he : X.Entails c (X.effectEq eff eff')) : Typing sig X solved c g e s eff' := by
  have hr := h.root
  obtain ⟨tree, ht⟩ := h
  exact ⟨.effectEq tree he, hr.1, hr.2.1, hr.2.2, ht⟩

theorem existsIntro {c g e a s eff} (h : Typing sig X solved c g e s eff)
    (hc : X.Admissible solved (X.existsNames a c))
    (hg : g.Avoids a) (hs : s.Avoids a) (he : Disjoint a.effects eff.vars) :
    Typing sig X solved (X.existsNames a c) g e s eff := by
  have hr := h.root
  obtain ⟨tree, ht⟩ := h
  exact ⟨.existsIntro hg hs he tree, hc, hr.2.1, hr.2.2, ht⟩

/-- Generalization preserves validity for the chosen solved set, provided the
projected constraint is admissible. No satisfiability-only replacement is used. -/
theorem generalize {c g e t} (h : Typing sig X solved c g e (.mono t) ∅)
    (hv : Value e) (a : Names) (fresh : g.Avoids a)
    (hc : X.Admissible solved (X.existsNames a c)) :
    Typing sig X solved (X.existsNames a c) g e (.qualified a c t) ∅ := by
  have andTop {d : X.Formula} (hd : X.Admissible solved d) :
      X.Admissible solved (X.and X.top d) := by
    obtain ⟨r, hr, h₁, h₂⟩ := hd
    exact ⟨r, hr, X.entails_trans (X.entails_right _ _) h₁,
      fun v hv => (X.holds_and _ _ v).mpr ⟨(X.holds_top v).mpr trivial, h₂ v hv⟩⟩
  have root := h.root
  obtain ⟨tree, valid⟩ := h
  refine ⟨tree.generalize hv a fresh, hc, root.2.1, root.1, ?_⟩
  exact ⟨andTop hc, root.2.1, root.1, andTop root.1, root.2.1, trivial, valid⟩

end Typing

/-- Full declarative validity for successful constraint-based inference.
The satisfiability check belongs to the solver, not to constraint generation. -/
theorem Inference.sound_valid {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {c g e t eff d}
    (h : Inference sig X N c g e t eff d)
    (hg : g.Admissible X.Satisfiable) (hd : X.Satisfiable d) :
    Typing sig X X.Satisfiable d g e (.mono t) eff ∧ X.Entails d c := by
  obtain ⟨⟨tree⟩, he⟩ := h.sound
  exact ⟨⟨tree, tree.valid_of_satisfiable hd hg⟩, he⟩

end EHMX.HMX
