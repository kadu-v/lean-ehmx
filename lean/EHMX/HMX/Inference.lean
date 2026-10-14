import EHMX.HMX.Generalization

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

namespace Constraints
variable (X : Constraints T O)

theorem conjunction_entails {cs : List X.Formula} {c : X.Formula}
    (hc : c ∈ cs) : X.Entails (X.conjunction cs) c :=
  fun v h => (X.holds_conjunction cs v).mp h c hc

def checked (input output : X.Formula) (actual expected : T.Term)
    (effect expectedEffect : Effect) : X.Formula :=
  X.conjunction [input, output, X.le actual expected, X.effectEq effect expectedEffect]

theorem holds_checked (input output : X.Formula) (actual expected : T.Term)
    (effect expectedEffect : Effect) (v : Valuation T.Value) :
    X.holds (X.checked input output actual expected effect expectedEffect) v ↔
      X.holds input v ∧ X.holds output v ∧ O.le (T.eval v actual) (T.eval v expected) ∧
        effect.eval v.effects = expectedEffect.eval v.effects := by
  simp [checked, X.holds_conjunction, X.holds_le, X.holds_effectEq]

theorem checked_input (c d : X.Formula) (a b : T.Term) (e f : Effect) :
    X.Entails (X.checked c d a b e f) c := X.conjunction_entails (by simp)

theorem checked_output (c d : X.Formula) (a b : T.Term) (e f : Effect) :
    X.Entails (X.checked c d a b e f) d := X.conjunction_entails (by simp)

def handler (c db dr dc : X.Formula) (decl : Operation T) (op : Op)
    (tr tc result : T.Term) (ein er eo rest out : Effect) (witnesses : Names) : X.Formula :=
  X.conjunction [c, db, dr, X.le tr result,
    X.clause decl.bound witnesses (X.and dc (X.and (X.le tc result) (X.effectLe eo out))),
    X.split op ein rest, X.effectLe rest out, X.effectLe er out]

end Constraints

/-- The rules expose child input constraints. A propagation policy chooses
these inputs; partial-solution obligations concern completeness, not soundness.
All comparisons of monotypes use the parameter relation. -/
inductive Inference (sig : Signature T) (X : Constraints T O) (N : X.Simplifier) :
    X.Formula → Context X → Expr → T.Term → Effect → X.Formula → Prop where
  | varMono {c g i t a eff} : g[i]? = some (.mono t) →
      Inference sig X N c g (.var i) a eff
        (X.checked c X.top t a ∅ eff)
  | varPoly {c g i bound d t a eff} (s : Substitution T) :
      g[i]? = some (.qualified bound d t) →
      s.domain.types ⊆ bound.types → s.domain.effects ⊆ bound.effects →
      Inference sig X N c g (.var i) a eff
        (X.checked c (X.subst s d) (s.apply t) a ∅ eff)
  | int {c g a eff} (n : Int) :
      Inference sig X N c g (.int n) a eff
        (X.checked c X.top (T.literal .int) a ∅ eff)
  | bool {c g a eff} (b : Bool) :
      Inference sig X N c g (.bool b) a eff
        (X.checked c X.top (T.literal .bool) a ∅ eff)
  | lam {c c₁ g body a b latent expected eff d} :
      Inference sig X N c₁ (.mono a :: g) body b latent d →
      Inference sig X N c g (.lam body) expected eff
        (X.checked c d (T.arrow a latent b) expected ∅ eff)
  | app {c c₁ c₂ g f x ft xt result ef ex latent eff d₁ d₂} :
      Inference sig X N c₁ g f ft ef d₁ →
      Inference sig X N c₂ g x xt ex d₂ →
      Inference sig X N c g (.app f x) result eff
        (X.conjunction [c, d₁, d₂, X.le ft (T.arrow xt latent result),
          X.effectEq (ef ∪ ex ∪ latent) eff])
  | letVal {c c₁ c₂ g v body a result eff d₁ d₂ bound} :
      Value v → g.Avoids bound →
      Inference sig X N c₁ g v a ∅ d₁ →
      Inference sig X N c₂ (.qualified bound (N.run d₁) a :: g) body result eff d₂ →
      Inference sig X N c g (.letE v body) result eff
        (X.conjunction [c, X.existsNames bound (N.run d₁), d₂])
  | letMono {c c₁ c₂ g v body a result ev eb eff d₁ d₂} :
      ¬ Value v →
      Inference sig X N c₁ g v a ev d₁ →
      Inference sig X N c₂ (.mono a :: g) body result eb d₂ →
      Inference sig X N c g (.letE v body) result eff
        (X.conjunction [c, d₁, d₂, X.effectEq (ev ∪ eb) eff])
  | perform {c c₁ g op raw arg a result ea eff d} (s : Substitution T) :
      sig op = some raw → raw.Closed →
      s.domain.types ⊆ raw.bound.types → s.domain.effects ⊆ raw.bound.effects →
      Inference sig X N c₁ g arg a ea d →
      Inference sig X N c g (.perform op arg) result eff
        (X.checked c (X.and d (X.le a (s.apply raw.input)))
          (s.apply raw.output) result (Effect.singleton op ∪ ea) eff)
  | handle {c cb cr cc g body op ret clause raw decl input result tr tc
      ein er eo rest out db dr dc witnesses} :
      sig op = some raw → raw.Closed → raw.FreshInstance decl →
      decl.Scoped X (X.handler c db dr dc decl op tr tc result ein er eo rest out witnesses)
        g input result ein er rest out witnesses →
      Inference sig X N cb g body input ein db →
      Inference sig X N cr (.mono input :: g) ret tr er dr →
      Inference sig X N cc
        (.mono (T.arrow decl.output out result) :: .mono decl.input :: g) clause tc eo dc →
      Inference sig X N c g (.handle body op ret clause) result out
        (X.handler c db dr dc decl op tr tc result ein er eo rest out witnesses)
  | check {c c₁ g e actual expected actualEffect expectedEffect d} :
      Inference sig X N c₁ g e actual actualEffect d →
      Inference sig X N c g e expected expectedEffect
        (X.checked c d actual expected actualEffect expectedEffect)
  | equivalent {c g e a eff d d'} :
      Inference sig X N c g e a eff d → X.Equivalent d' d →
      Inference sig X N c g e a eff d'
  | project {c g e t eff d hidden} :
      g.Avoids hidden → (Scheme.mono (X := X) t).Avoids hidden →
      Disjoint hidden.effects eff.vars → hidden.Disjoint (X.support c) →
      Inference sig X N c g e t eff d →
      Inference sig X N c g e t eff (X.existsNames hidden d)

def Derivation.check {sig : Signature T} {X : Constraints T O}
    {c d : X.Formula} {g : Context X} {e : Expr} {a b : T.Term} {ea eb : Effect}
    (tree : Derivation sig X d g e (.mono a) ea) :
    Derivation sig X (X.checked c d a b ea eb) g e (.mono b) eb := by
  apply Derivation.effectEq
  · apply Derivation.sub
    · exact .weaken tree (X.checked_output _ _ _ _ _ _)
    · exact X.conjunction_entails (by simp)
  · exact X.conjunction_entails (by simp)

/-- Constraint-generation soundness is independent of the propagation policy.
The conclusion is derivability; validity additionally checks admissibility of
the constraints at every node via `Derivation.Valid`. -/
theorem Inference.sound {sig : Signature T} {X : Constraints T O} {N : X.Simplifier}
    {c g e a eff d} (h : Inference sig X N c g e a eff d) :
    Nonempty (Derivation sig X d g e (.mono a) eff) ∧ X.Entails d c := by
  induction h with
  | varMono found =>
      exact ⟨⟨(Derivation.var found).check⟩, X.conjunction_entails (by simp)⟩
  | varPoly s found ht he =>
      have tree := Derivation.forallElim (sig := sig) s ht he (Derivation.var found)
        (X.entails_refl _)
      exact ⟨⟨tree.check⟩, X.conjunction_entails (by simp)⟩
  | int n => exact ⟨⟨(Derivation.int n).check⟩, X.conjunction_entails (by simp)⟩
  | bool b => exact ⟨⟨(Derivation.bool b).check⟩, X.conjunction_entails (by simp)⟩
  | lam _ ih =>
      obtain ⟨tree⟩ := ih.1
      exact ⟨⟨(Derivation.lam tree).check⟩, X.checked_input _ _ _ _ _ _⟩
  | @app c c₁ c₂ g f x ft xt result ef ex latent eff d₁ d₂ _ _ ihf ihx =>
      obtain ⟨tf⟩ := ihf.1
      obtain ⟨tx⟩ := ihx.1
      refine ⟨⟨?_⟩, X.conjunction_entails (by simp)⟩
      apply Derivation.effectEq (eff := ef ∪ ex ∪ latent)
      · apply Derivation.app (a := xt) (latent := latent)
        · apply Derivation.sub
          · exact .weaken tf (X.conjunction_entails (by simp))
          · exact X.conjunction_entails (by simp)
        · exact .weaken tx (X.conjunction_entails (by simp))
      · exact X.conjunction_entails (by simp)
  | letVal hv fresh _ _ ihv ihb =>
      obtain ⟨tv⟩ := ihv.1
      obtain ⟨tb⟩ := ihb.1
      refine ⟨⟨?_⟩, X.conjunction_entails (by simp)⟩
      apply Derivation.letVal hv
      · exact .weaken (tv.generalize_normalized hv N _ fresh)
          (X.conjunction_entails (by simp))
      · exact .weaken tb (X.conjunction_entails (by simp))
  | letMono hv _ _ ihv ihb =>
      obtain ⟨tv⟩ := ihv.1
      obtain ⟨tb⟩ := ihb.1
      refine ⟨⟨?_⟩, X.conjunction_entails (by simp)⟩
      apply Derivation.effectEq
      · exact .letMono hv
          (.weaken tv (X.conjunction_entails (by simp)))
          (.weaken tb (X.conjunction_entails (by simp)))
      · exact X.conjunction_entails (by simp)
  | @perform c c₁ g op raw arg a result ea eff d s hs hc ht he _ ih =>
      obtain ⟨tree⟩ := ih.1
      have argument := Derivation.sub (b := s.apply raw.input)
        (Derivation.weaken tree (X.entails_left _ _)) (X.entails_right _ _)
      exact ⟨⟨(Derivation.perform s hs hc ht he argument).check⟩,
        X.checked_input _ _ _ _ _ _⟩
  | handle hs hc hf scope _ _ _ ihb ihr ihc =>
      obtain ⟨tb⟩ := ihb.1
      obtain ⟨tr⟩ := ihr.1
      obtain ⟨tc⟩ := ihc.1
      refine ⟨⟨?_⟩, X.conjunction_entails (by simp)⟩
      apply Derivation.handle hs hc hf scope.context scope.rigid_types
        scope.rigid_effects scope.witness_scope scope.witness_constraint scope.witness_effects
      · exact .weaken tb (X.conjunction_entails (by simp))
      · exact .sub (.weaken tr (X.conjunction_entails (by simp)))
          (X.conjunction_entails (by simp))
      · exact tc
      · exact X.conjunction_entails (by simp)
      · exact X.conjunction_entails (by simp)
      · exact X.conjunction_entails (by simp)
      · exact X.conjunction_entails (by simp)
  | check _ ih =>
      obtain ⟨tree⟩ := ih.1
      exact ⟨⟨tree.check⟩, X.checked_input _ _ _ _ _ _⟩
  | equivalent _ hd ih =>
      obtain ⟨tree⟩ := ih.1
      exact ⟨⟨.weaken tree hd.1⟩, X.entails_trans hd.1 ih.2⟩
  | project hg ht he hc _ ih =>
      obtain ⟨tree⟩ := ih.1
      exact ⟨⟨.existsIntro hg ht he tree⟩,
        X.entails_trans (X.exists_mono _ ih.2) (X.project_independent _ _ hc).1⟩

end EHMX.HMX
