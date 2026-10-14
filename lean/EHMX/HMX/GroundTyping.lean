import EHMX.HMX.Instantiation

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

abbrev GroundContext (T : TypeDomain) := List (Set T.Value)

def upper (O : TypeOrder T) (a : T.Value) : Set T.Value := {b | O.le a b}

theorem effect_eval_union (e f : Effect) (v : Nat → Finset Op) :
    (e ∪ f).eval v = e.eval v ∪ f.eval v := by
  ext op
  simp only [Effect.eval, Finset.mem_union, Finset.mem_biUnion]
  aesop

theorem effect_eval_singleton (op : Op) (v : Nat → Finset Op) :
    (Effect.singleton op).eval v = {op} := by
  simp [Effect.eval, Effect.singleton]

def Context.ground {X : Constraints T O} (g : Context X)
    (v : Valuation T.Value) : GroundContext T :=
  g.map (fun s => {t | s.GroundInstance v t})

def Context.GroundRealizable {X : Constraints T O} (g : Context X)
    (v : Valuation T.Value) : Prop := ∀ s ∈ g, ∃ t, s.GroundInstance v t

theorem Context.GroundRealizable.cons_mono {X : Constraints T O} {g : Context X}
    {v : Valuation T.Value} (h : g.GroundRealizable v) (t : T.Term) :
    Context.GroundRealizable (.mono t :: g) v := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ⟨T.eval v t, O.refl _⟩
  · exact h s hs

theorem Context.GroundRealizable.avoids {X : Constraints T O} {g : Context X}
    {v w : Valuation T.Value} {a : Names} (h : g.GroundRealizable v)
    (hg : g.Avoids a) (hw : w.AgreeOutside v a) : g.GroundRealizable w := by
  intro s hs
  obtain ⟨t, ht⟩ := h s hs
  exact ⟨t, (Scheme.groundInstance_avoids (hg s hs) hw t).mpr ht⟩

theorem Context.Realizable.ground {X : Constraints T O} {g : Context X}
    {c : X.Formula} (h : g.Realizable c) {v : Valuation T.Value} (hc : X.holds c v) :
    g.GroundRealizable v := fun s hs => (h s hs).groundInstance hc

theorem Derivation.groundInstance_exists {sig : Signature T} {X : Constraints T O}
    {c g e s eff} (tree : Derivation sig X c g e s eff)
    (v : Valuation T.Value) (hc : X.holds c v) (hg : g.GroundRealizable v) :
    ∃ t, s.GroundInstance v t := by
  induction tree generalizing v with
  | var found => exact hg _ (List.mem_of_getElem? found)
  | int | bool | lam | app | letVal | letMono | sub | forallElim | perform | handle =>
      exact ⟨_, O.refl _⟩
  | forallIntro hv ha hga body ih =>
      obtain ⟨w, hw, hd⟩ := (X.holds_exists _ _ v).mp ((X.holds_and _ _ v).mp hc).2
      exact ⟨_, w, hw, hd, O.refl _⟩
  | existsIntro hga hsa hea body ih =>
      obtain ⟨w, hw, hd⟩ := (X.holds_exists _ _ v).mp hc
      obtain ⟨t, ht⟩ := ih w hd (hg.avoids hga hw)
      exact ⟨t, (Scheme.groundInstance_avoids hsa hw t).mp ht⟩
  | weaken body he ih => exact ih v (he v hc) hg
  | effectEq body he ih => exact ih v hc hg
  | alpha body he ih =>
      obtain ⟨t, ht⟩ := ih v hc hg
      exact ⟨t, (he.groundInstance_iff v t).mp ht⟩

theorem Context.ground_cons_mono {X : Constraints T O} (t : T.Term)
    (g : Context X) (v : Valuation T.Value) :
    Context.ground (.mono t :: g) v = upper O (T.eval v t) :: g.ground v := rfl

theorem Context.ground_avoids {X : Constraints T O} {g : Context X} {a : Names}
    (hg : g.Avoids a) {v w : Valuation T.Value} (hw : v.AgreeOutside w a) :
    g.ground v = g.ground w := by
  apply List.map_congr_left
  intro s hs
  ext t
  exact Scheme.groundInstance_avoids (hg s hs) hw t

theorem TypeDomain.eval_agreeOutside (t : T.Term) {a : Names}
    (ha : a.Disjoint (T.support t)) {v w : Valuation T.Value}
    (hw : v.AgreeOutside w a) : T.eval v t = T.eval w t :=
  T.eval_support v w t
    ⟨fun i hi => hw.1 i (fun hm => Finset.disjoint_left.mp ha.1 hm hi),
      fun i hi => hw.2 i (fun hm => Finset.disjoint_left.mp ha.2 hm hi)⟩

theorem effect_eval_agreeOutside (e : Effect) {a : Names}
    (ha : Disjoint a.effects e.vars) {v w : Valuation T.Value}
    (hw : v.AgreeOutside w a) : e.eval v.effects = e.eval w.effects := by
  unfold Effect.eval
  congr 1
  apply Finset.biUnion_congr rfl
  intro i hi
  exact hw.2 i (fun hm => Finset.disjoint_left.mp ha hm hi)

theorem Operation.freshInstance_eval {raw decl : Operation T}
    (hc : raw.Closed) (hf : raw.FreshInstance decl)
    {v w : Valuation T.Value} (hw : v.AgreeOn w decl.bound) :
    T.eval v decl.input = T.eval w decl.input ∧
    T.eval v decl.output = T.eval w decl.output := by
  obtain ⟨f, g, _, _, rfl⟩ := hf
  simp only [Operation.rename, T.eval_rename]
  constructor <;> apply T.eval_support <;> constructor
  · intro i hi; exact hw.1 (f i) (Finset.mem_image.mpr ⟨i, hc.1 (Finset.mem_union_left _ hi), rfl⟩)
  · intro i hi; exact hw.2 (g i) (Finset.mem_image.mpr ⟨i, hc.2 (Finset.mem_union_left _ hi), rfl⟩)
  · intro i hi; exact hw.1 (f i) (Finset.mem_image.mpr ⟨i, hc.1 (Finset.mem_union_right _ hi), rfl⟩)
  · intro i hi; exact hw.2 (g i) (Finset.mem_image.mpr ⟨i, hc.2 (Finset.mem_union_right _ hi), rfl⟩)

/-- Ground typing has no constraint solver or generalization algorithm.
Value-let binds a set of instances; a handler clause must work for every
ground instantiation of its operation parameters. -/
inductive GroundTyping (sig : Signature T) (O : TypeOrder T) :
    GroundContext T → Expr → T.Value → Finset Op → Prop where
  | var {g i s t} : g[i]? = some s → t ∈ s → GroundTyping sig O g (.var i) t ∅
  | int {g} (n : Int) : GroundTyping sig O g (.int n) (T.groundLiteral .int) ∅
  | bool {g} (b : Bool) : GroundTyping sig O g (.bool b) (T.groundLiteral .bool) ∅
  | lam {g body a b eff} : GroundTyping sig O (upper O a :: g) body b eff →
      GroundTyping sig O g (.lam body) (T.groundArrow a eff b) ∅
  | app {g f x a b ef ex latent} :
      GroundTyping sig O g f (T.groundArrow a latent b) ef →
      GroundTyping sig O g x a ex →
      GroundTyping sig O g (.app f x) b (ef ∪ ex ∪ latent)
  | letVal {g v body s t eff} : Value v →
      s.Nonempty →
      (∀ a ∈ s, GroundTyping sig O g v a ∅) →
      GroundTyping sig O (s :: g) body t eff →
      GroundTyping sig O g (.letE v body) t eff
  | letMono {g v body a b ev eb} : ¬ Value v →
      GroundTyping sig O g v a ev → GroundTyping sig O (upper O a :: g) body b eb →
      GroundTyping sig O g (.letE v body) b (ev ∪ eb)
  | sub {g e a b eff} : GroundTyping sig O g e a eff → O.le a b →
      GroundTyping sig O g e b eff
  | perform {g op raw arg eff} (v : Valuation T.Value) :
      sig op = some raw → raw.Closed → GroundTyping sig O g arg (T.eval v raw.input) eff →
      GroundTyping sig O g (.perform op arg) (T.eval v raw.output) ({op} ∪ eff)
  | handle {g body op ret clause raw decl input result ein er rest out}
      (clauseEffects : Valuation T.Value → Finset Op) :
      sig op = some raw → raw.Closed → raw.FreshInstance decl →
      GroundTyping sig O g body input ein →
      GroundTyping sig O (upper O input :: g) ret result er →
      (∀ w : Valuation T.Value,
        GroundTyping sig O
          (upper O (T.groundArrow (T.eval w decl.output) out result) ::
            upper O (T.eval w decl.input) :: g) clause result (clauseEffects w)) →
      (∀ w, clauseEffects w ⊆ out) →
      rest ⊆ ein → ein ⊆ {op} ∪ rest → op ∉ rest → rest ⊆ out → er ⊆ out →
      GroundTyping sig O g (.handle body op ret clause) result out

theorem Derivation.ground {sig : Signature T} {X : Constraints T O}
    {c g e s eff} (tree : Derivation sig X c g e s eff)
    (v : Valuation T.Value) (hc : X.holds c v)
    (hg : g.GroundRealizable v)
    (u : T.Value) (hu : s.GroundInstance v u) :
    GroundTyping sig O (g.ground v) e u (eff.eval v.effects) := by
  induction tree generalizing v u with
  | @var c g i s found =>
      apply GroundTyping.var (s := {t | s.GroundInstance v t})
      · simp [Context.ground, List.getElem?_map, found]
      · exact hu
  | int n => exact .sub (.int n) (by simpa [Scheme.GroundInstance, T.eval_literal] using hu)
  | bool b => exact .sub (.bool b) (by simpa [Scheme.GroundInstance, T.eval_literal] using hu)
  | lam body ih =>
      apply GroundTyping.sub (GroundTyping.lam (ih v hc (hg.cons_mono _) _ (O.refl _)))
      simpa [Scheme.GroundInstance, T.eval_arrow] using hu
  | app f x ihf ihx =>
      have hf := ihf v hc hg _ (O.refl _)
      rw [T.eval_arrow] at hf
      simpa only [effect_eval_union] using
        GroundTyping.sub (GroundTyping.app hf (ihx v hc hg _ (O.refl _))) hu
  | @letVal c g valExpr bodyExpr s t eff hv val body ihv ihb =>
      have hval := val.groundInstance_exists v hc hg
      have hgb : Context.GroundRealizable (s :: g) v := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hval
        · exact hg s hs
      exact GroundTyping.sub (GroundTyping.letVal hv hval (fun a ha => ihv v hc hg a ha)
        (ihb v hc hgb _ (O.refl _))) hu
  | letMono hv val body ihv ihb =>
      simpa only [effect_eval_union] using
        GroundTyping.sub (GroundTyping.letMono hv (ihv v hc hg _ (O.refl _))
          (ihb v hc (hg.cons_mono _) _ (O.refl _))) hu
  | sub body he ih =>
      exact ih v hc hg u (O.trans ((X.holds_le _ _ v).mp (he v hc)) hu)
  | forallIntro hv ha hga body ih =>
      obtain ⟨w, hw, hd, ht⟩ := hu
      have hc' := (X.holds_agreeOutside ha hw).mpr ((X.holds_and _ _ v).mp hc).1
      have h := ih w ((X.holds_and _ _ w).mpr ⟨hc', hd⟩) (hg.avoids hga hw) u ht
      have hctx := Context.ground_avoids hga hw
      rw [hctx] at h
      exact h
  | forallElim sub ht he body hd ih =>
      apply ih v hc hg u
      refine ⟨sub.pullback v, ⟨?_, ?_⟩, (X.holds_subst _ _ v).mp (hd v hc), ?_⟩
      · intro i hi; exact (sub.pullback_outside v).1 i (fun hm => hi (ht hm))
      · intro i hi; exact (sub.pullback_outside v).2 i (fun hm => hi (he hm))
      · simpa only [Scheme.GroundInstance, sub.eval_apply] using hu
  | existsIntro hga hs he body ih =>
      obtain ⟨w, hw, hd⟩ := (X.holds_exists _ _ v).mp hc
      have h := ih w hd (hg.avoids hga hw) u ((Scheme.groundInstance_avoids hs hw u).mpr hu)
      simpa only [Context.ground_avoids hga hw, effect_eval_agreeOutside _ he hw] using h
  | weaken body he ih => exact ih v (he v hc) hg u hu
  | effectEq body he ih =>
      simpa only [← (X.holds_effectEq _ _ v).mp (he v hc)] using ih v hc hg u hu
  | alpha body he ih => exact ih v hc hg u ((he.groundInstance_iff v u).mpr hu)
  | perform sub hs hclosed ht he body ih =>
      have h := ih v hc hg _ (O.refl _)
      simp only [Scheme.GroundInstance, sub.eval_apply] at h hu
      simpa only [effect_eval_union, effect_eval_singleton] using
        GroundTyping.sub (GroundTyping.perform (sub.pullback v) hs hclosed h) hu
  | @handle c d g body op ret clause raw decl input result clauseTy
      ein er eo rest out witnesses hs hclosed fresh hga htypes heffects hwscope hwconstraint hwe
      tb tr tc hh hsplit hr her ihb ihr ihc =>
      have heout : Disjoint decl.bound.effects out.vars :=
        heffects.mono_right (by intro i hi; simp only [Finset.mem_union]; exact .inr hi)
      have htresult : decl.bound.Disjoint (T.support result) :=
        ⟨htypes.1.mono_right Finset.subset_union_right,
          htypes.2.mono_right Finset.subset_union_right⟩
      have hwg : witnesses.Disjoint g.support := by
        constructor
        · exact hwscope.1.mono_right Finset.subset_union_left
        · exact hwscope.2.mono_right Finset.subset_union_left
      have hwresult : witnesses.Disjoint (T.support result) := by
        constructor
        · exact hwscope.1.mono_right (by intro i hi; simp only [Names.union, Finset.mem_union]; exact .inr (.inl (.inr hi)))
        · exact hwscope.2.mono_right (by intro i hi; simp only [Names.union, Finset.mem_union]; exact .inr (.inl (.inr hi)))
      have hwinput : witnesses.Disjoint (T.support decl.input) := by
        constructor
        · exact hwscope.1.mono_right (by intro i hi; simp only [Names.union, Finset.mem_union]; exact .inr (.inr (.inl (.inl hi))))
        · exact hwscope.2.mono_right (by intro i hi; simp only [Names.union, Finset.mem_union]; exact .inr (.inr (.inl (.inl hi))))
      have hwoutput : witnesses.Disjoint (T.support decl.output) := by
        constructor
        · exact hwscope.1.mono_right (by intro i hi; simp only [Names.union, Finset.mem_union]; exact .inr (.inr (.inl (.inr hi))))
        · exact hwscope.2.mono_right (by intro i hi; simp only [Names.union, Finset.mem_union]; exact .inr (.inr (.inl (.inr hi))))
      have hweout : Disjoint witnesses.effects out.vars :=
        hwe.mono_right (by intro i hi; simp only [Finset.mem_union]; exact .inr hi)
      have hcground (w : Valuation T.Value) : ∃ eff,
          GroundTyping sig O
            (upper O (T.groundArrow (T.eval w decl.output) (out.eval v.effects)
              (T.eval v result)) :: upper O (T.eval w decl.input) :: g.ground v)
            clause (T.eval v result) eff ∧ eff ⊆ out.eval v.effects := by
        let w' := v.patch w decl.bound
        have hp := v.patch_agreeOutside w decl.bound
        obtain ⟨z, hz, hdz⟩ := (X.holds_clause _ _ _ v).mp (hh v hc) w' hp
        obtain ⟨hd, hle, he⟩ := (X.holds_and _ _ z).mp hdz |>.imp_right (fun h => (X.holds_and _ _ z).mp h)
        have hg' : g.ground z = g.ground v :=
          (Context.ground_avoids (g.avoids_of_support_disjoint witnesses hwg) hz).trans
            (Context.ground_avoids hga hp)
        have hresult : T.eval z result = T.eval v result :=
          (TypeDomain.eval_agreeOutside result hwresult hz).trans
            (TypeDomain.eval_agreeOutside result htresult hp)
        have hout : out.eval z.effects = out.eval v.effects :=
          (effect_eval_agreeOutside out hweout hz).trans (effect_eval_agreeOutside out heout hp)
        have hdecl := Operation.freshInstance_eval hclosed fresh
          (v := w') (w := w) (by constructor <;> intro i hi <;> simp [w', Valuation.patch, hi])
        have hin : T.eval z decl.input = T.eval w decl.input :=
          (TypeDomain.eval_agreeOutside decl.input hwinput hz).trans hdecl.1
        have houtput : T.eval z decl.output = T.eval w decl.output :=
          (TypeDomain.eval_agreeOutside decl.output hwoutput hz).trans hdecl.2
        have hgz := (hg.avoids hga hp).avoids (g.avoids_of_support_disjoint witnesses hwg) hz
        have h := ihc z hd ((hgz.cons_mono _).cons_mono _)
          (T.eval z result) ((X.holds_le _ _ z).mp hle)
        refine ⟨eo.eval z.effects, ?_, ?_⟩
        · simpa only [Context.ground_cons_mono,
            T.eval_arrow, hin, houtput, hresult, hout, hg'] using h
        · simpa only [hout] using (X.holds_effectLe _ _ z).mp he
      classical
      choose ceff hceff hcle using hcground
      obtain ⟨hs₁, hs₂, hs₃⟩ := (X.holds_and _ _ v).mp (hsplit v hc) |>.imp_right (fun h => (X.holds_and _ _ v).mp h)
      have h := GroundTyping.handle ceff hs hclosed fresh
        (ihb v hc hg _ (O.refl _)) (ihr v hc (hg.cons_mono _) _ (O.refl _)) hceff hcle
        ((X.holds_effectLe _ _ v).mp hs₁)
        (by simpa only [effect_eval_union, effect_eval_singleton] using (X.holds_effectLe _ _ v).mp hs₂)
        ((X.holds_lacks _ _ v).mp hs₃)
        ((X.holds_effectLe _ _ v).mp (hr v hc))
        ((X.holds_effectLe _ _ v).mp (her v hc))
      exact .sub h hu

end EHMX.HMX


namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

theorem Context.member_support {X : Constraints T O} {g : Context X} {s : Scheme X}
    (hs : s ∈ g) : s.support.types ⊆ g.support.types ∧
      s.support.effects ⊆ g.support.effects := by
  induction g with
  | nil => cases hs
  | cons t g ih =>
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨Finset.subset_union_left, Finset.subset_union_left⟩
      · have h := ih hs
        exact ⟨h.1.trans Finset.subset_union_right, h.2.trans Finset.subset_union_right⟩

theorem Context.ground_support {X : Constraints T O} {g : Context X}
    {v w : Valuation T.Value} (h : v.AgreeOn w g.support) : g.ground v = g.ground w := by
  apply List.map_congr_left
  intro s hs
  have hsub := Context.member_support hs
  ext t
  exact s.groundInstance_support v w
    (fun i hi => h.1 i (hsub.1 (Scheme.freeType_mem_support hi)))
    (fun i hi => h.2 i (hsub.2 (Scheme.freeEffect_mem_support hi))) t

/-- Every variable instance offered by the first context is offered by the
second at the same de Bruijn index. -/
def GroundContext.CoveredBy (g d : GroundContext T) : Prop :=
  ∀ (i : Nat) s, g[i]? = some s → ∀ t ∈ s, ∃ s', d[i]? = some s' ∧ t ∈ s'

theorem GroundContext.CoveredBy.refl (g : GroundContext T) : g.CoveredBy g :=
  fun _ s hs _ ht => ⟨s, hs, ht⟩

theorem GroundContext.CoveredBy.cons {g d : GroundContext T} (h : g.CoveredBy d)
    {s t : Set T.Value} (hst : s ⊆ t) : GroundContext.CoveredBy (s :: g) (t :: d) := by
  intro i u hu a ha
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
      subst u
      exact ⟨t, rfl, hst ha⟩
  | succ i => exact h i u hu a ha

theorem Context.MoreGeneralAt.ground {X : Constraints T O}
    {g d : Context X} {v w : Valuation T.Value} (h : g.MoreGeneralAt d v w) :
    (d.ground w).CoveredBy (g.ground v) := by
  induction h with
  | nil =>
      intro i s hs
      simp [Context.ground] at hs
  | @cons s t g d hst hgd ih =>
      exact ih.cons hst

theorem GroundTyping.context_mono {sig : Signature T} {g d : GroundContext T}
    {e t eff} (h : GroundTyping sig O g e t eff) (hgd : g.CoveredBy d) :
    GroundTyping sig O d e t eff := by
  induction h generalizing d with
  | var hs ht =>
      obtain ⟨s, hs, ht⟩ := hgd _ _ hs _ ht
      exact .var hs ht
  | int n => exact .int n
  | bool b => exact .bool b
  | lam body ih => exact .lam (ih (hgd.cons (Set.Subset.refl _)))
  | app f x ihf ihx => exact .app (ihf hgd) (ihx hgd)
  | letVal hv hne val body ihv ihb =>
      exact .letVal hv hne (fun a ha => ihv a ha hgd) (ihb (hgd.cons (Set.Subset.refl _)))
  | letMono hv val body ihv ihb =>
      exact .letMono hv (ihv hgd) (ihb (hgd.cons (Set.Subset.refl _)))
  | sub body ht ih => exact .sub (ih hgd) ht
  | perform v hs hc body ih => exact .perform v hs hc (ih hgd)
  | handle ceff hs hc hf body ret clause hce h₁ h₂ h₃ h₄ h₅ ihb ihr ihc =>
      exact .handle ceff hs hc hf (ihb hgd) (ihr (hgd.cons (Set.Subset.refl _)))
        (fun w => ihc w ((hgd.cons (Set.Subset.refl _)).cons (Set.Subset.refl _)))
        hce h₁ h₂ h₃ h₄ h₅

end EHMX.HMX


namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

theorem GroundTyping.value_effect {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) (hv : Value e) : eff = ∅ := by
  induction h with
  | var | int | bool | lam => rfl
  | sub _ _ ih => exact ih hv
  | app | letVal | letMono | perform | handle => cases hv

theorem GroundTyping.int_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {n : Int} (he : e = .int n) :
    O.le (T.groundLiteral .int) t ∧ eff = ∅ := by
  induction h with
  | int => exact ⟨O.refl _, rfl⟩
  | sub hb ht ih =>
      have hi := ih he
      exact ⟨O.trans hi.1 ht, hi.2⟩
  | _ => cases he

theorem GroundTyping.bool_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {b : Bool} (he : e = .bool b) :
    O.le (T.groundLiteral .bool) t ∧ eff = ∅ := by
  induction h with
  | bool => exact ⟨O.refl _, rfl⟩
  | sub hb ht ih =>
      have hi := ih he
      exact ⟨O.trans hi.1 ht, hi.2⟩
  | _ => cases he

theorem GroundTyping.var_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {i : Nat} (he : e = .var i) :
    (∃ s a, g[i]? = some s ∧ a ∈ s ∧ O.le a t) ∧ eff = ∅ := by
  induction h with
  | var found hm => cases he; exact ⟨⟨_, _, found, hm, O.refl _⟩, rfl⟩
  | sub body ht ih =>
      obtain ⟨⟨s, a, hs, ha, hat⟩, heff⟩ := ih he
      exact ⟨⟨s, a, hs, ha, O.trans hat ht⟩, heff⟩
  | _ => cases he

theorem GroundTyping.lam_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {body : Expr} (he : e = .lam body) :
    (∃ a b latent, GroundTyping sig O (upper O a :: g) body b latent ∧
      O.le (T.groundArrow a latent b) t) ∧ eff = ∅ := by
  induction h with
  | lam hb ih => cases he; exact ⟨⟨_, _, _, hb, O.refl _⟩, rfl⟩
  | sub hb ht ih =>
      obtain ⟨⟨a, b, latent, hb, hle⟩, heff⟩ := ih he
      exact ⟨⟨a, b, latent, hb, O.trans hle ht⟩, heff⟩
  | _ => cases he

theorem GroundTyping.app_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {f x : Expr} (he : e = .app f x) :
    ∃ a ef ex latent,
      GroundTyping sig O g f (T.groundArrow a latent t) ef ∧
      GroundTyping sig O g x a ex ∧ eff = ef ∪ ex ∪ latent := by
  induction h with
  | app hf hx ihf ihx => cases he; exact ⟨_, _, _, _, hf, hx, rfl⟩
  | sub hb ht ih =>
      obtain ⟨a, ef, ex, latent, hf, hx, heff⟩ := ih he
      exact ⟨a, ef, ex, latent, .sub hf (O.arrow latent (O.refl a) ht), hx, heff⟩
  | _ => cases he

theorem GroundTyping.letVal_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {val body : Expr}
    (he : e = .letE val body) (hv : Value val) :
    ∃ s : Set T.Value, s.Nonempty ∧ (∀ a ∈ s, GroundTyping sig O g val a ∅) ∧
      GroundTyping sig O (s :: g) body t eff := by
  induction h with
  | letVal hv hne hval hbody ihv ihb => cases he; exact ⟨_, hne, hval, hbody⟩
  | letMono hn hval hbody ihv ihb => cases he; exact False.elim (hn hv)
  | sub hb ht ih =>
      obtain ⟨s, hne, hval, hbody⟩ := ih he
      exact ⟨s, hne, hval, .sub hbody ht⟩
  | _ => cases he

theorem GroundTyping.letMono_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {val body : Expr}
    (he : e = .letE val body) (hv : ¬ Value val) :
    ∃ a ev eb, GroundTyping sig O g val a ev ∧
      GroundTyping sig O (upper O a :: g) body t eb ∧ eff = ev ∪ eb := by
  induction h with
  | letVal hval hne h₁ h₂ ih₁ ih₂ => cases he; exact False.elim (hv hval)
  | letMono hn hval hbody ihv ihb => cases he; exact ⟨_, _, _, hval, hbody, rfl⟩
  | sub hb ht ih =>
      obtain ⟨a, ev, eb, hval, hbody, heff⟩ := ih he
      exact ⟨a, ev, eb, hval, .sub hbody ht, heff⟩
  | _ => cases he

theorem GroundTyping.perform_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {op : Op} {arg : Expr} (he : e = .perform op arg) :
    ∃ raw, sig op = some raw ∧ raw.Closed ∧ ∃ v ea,
      GroundTyping sig O g arg (T.eval v raw.input) ea ∧
      O.le (T.eval v raw.output) t ∧ eff = {op} ∪ ea := by
  induction h with
  | perform v hs hc harg ih => cases he; exact ⟨_, hs, hc, v, _, harg, O.refl _, rfl⟩
  | sub hb ht ih =>
      obtain ⟨raw, hs, hc, v, ea, harg, hle, heff⟩ := ih he
      exact ⟨raw, hs, hc, v, ea, harg, O.trans hle ht, heff⟩
  | _ => cases he

theorem Operation.freshInstance_realizes {raw decl : Operation T}
    (hc : raw.Closed) (hf : raw.FreshInstance decl) (z : Valuation T.Value) :
    ∃ w, T.eval w decl.input = T.eval z raw.input ∧
      T.eval w decl.output = T.eval z raw.output := by
  obtain ⟨ft, fe, ht, he, rfl⟩ := hf
  let w := z.assignImages z raw.bound ft fe
  refine ⟨w, ?_, ?_⟩ <;> simp only [Operation.rename, T.eval_rename] <;>
    apply T.eval_support <;> constructor
  · intro i hi; exact z.assignImages_types z raw.bound ft fe ht i (hc.1 (Finset.mem_union_left _ hi))
  · intro i hi; exact z.assignImages_effects z raw.bound ft fe he i (hc.2 (Finset.mem_union_left _ hi))
  · intro i hi; exact z.assignImages_types z raw.bound ft fe ht i (hc.1 (Finset.mem_union_right _ hi))
  · intro i hi; exact z.assignImages_effects z raw.bound ft fe he i (hc.2 (Finset.mem_union_right _ hi))

theorem GroundTyping.handle_inv {sig : Signature T} {g : GroundContext T}
    {e : Expr} {t : T.Value} {eff : Finset Op}
    (h : GroundTyping sig O g e t eff) {body ret clause : Expr} {op : Op}
    (he : e = .handle body op ret clause) :
    ∃ raw, sig op = some raw ∧ raw.Closed ∧ ∃ input result ein er rest,
      GroundTyping sig O g body input ein ∧
      GroundTyping sig O (upper O input :: g) ret result er ∧
      (∀ z : Valuation T.Value, ∃ eo,
        GroundTyping sig O (upper O (T.groundArrow (T.eval z raw.output) eff result) ::
          upper O (T.eval z raw.input) :: g) clause result eo ∧ eo ⊆ eff) ∧
      rest ⊆ ein ∧ ein ⊆ {op} ∪ rest ∧ op ∉ rest ∧ rest ⊆ eff ∧ er ⊆ eff ∧ O.le result t := by
  induction h with
  | handle ceff hs hc hf hb hr hcl hce h₁ h₂ h₃ h₄ h₅ ihb ihr ihc =>
      cases he
      refine ⟨_, hs, hc, _, _, _, _, _, hb, hr, ?_, h₁, h₂, h₃, h₄, h₅, O.refl _⟩
      intro z
      obtain ⟨w, hin, hout⟩ := Operation.freshInstance_realizes hc hf z
      exact ⟨ceff w, by simpa only [hin, hout] using hcl w, hce w⟩
  | sub hb ht ih =>
      obtain ⟨raw, hs, hc, input, result, ein, er, rest, hb, hr, hcl, h₁, h₂, h₃, h₄, h₅, hle⟩ := ih he
      exact ⟨raw, hs, hc, input, result, ein, er, rest, hb, hr, hcl, h₁, h₂, h₃, h₄, h₅, O.trans hle ht⟩
  | _ => cases he

end EHMX.HMX
