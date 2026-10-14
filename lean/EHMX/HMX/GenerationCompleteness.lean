import EHMX.HMX.Algorithm

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- Extend a valuation above finite protected names. This is a valuation,
not an infinite substitution supplied to normalization. -/
def Valuation.fresh {V : Type} (v : Valuation V) (fixed : Names)
    (types : Nat → V) (effects : Nat → Finset Op) : Valuation V :=
  ⟨fun i => if i ≤ fixed.types.sup id then v.types i else types (i - (fixed.types.sup id + 1)),
    fun i => if i ≤ fixed.effects.sup id then v.effects i else effects (i - (fixed.effects.sup id + 1))⟩

theorem Valuation.fresh_agree {V : Type} (v : Valuation V) (fixed : Names)
    (types : Nat → V) (effects : Nat → Finset Op) :
    (v.fresh fixed types effects).AgreeOn v fixed := by
  constructor
  · intro i hi
    have hle : i ≤ fixed.types.sup id := Finset.le_sup (f := id) hi
    simp [Valuation.fresh, hle]
  · intro i hi
    have hle : i ≤ fixed.effects.sup id := Finset.le_sup (f := id) hi
    simp [Valuation.fresh, hle]

theorem Valuation.fresh_types {V : Type} (v : Valuation V) (fixed : Names)
    (types : Nat → V) (effects : Nat → Finset Op) (i : Nat) :
    (v.fresh fixed types effects).types (fixed.shiftTypes i) = types i := by
  have h : ¬ fixed.types.sup id + 1 + i ≤ fixed.types.sup id := by omega
  simp [Valuation.fresh, Names.shiftTypes, h]

theorem Valuation.fresh_effects {V : Type} (v : Valuation V) (fixed : Names)
    (types : Nat → V) (effects : Nat → Finset Op) (i : Nat) :
    (v.fresh fixed types effects).effects (fixed.shiftEffects i) = effects i := by
  have h : ¬ fixed.effects.sup id + 1 + i ≤ fixed.effects.sup id := by omega
  simp [Valuation.fresh, Names.shiftEffects, h]

theorem Inference.Protected.context {X : Constraints T O} (g : Context X) (t : T.Term)
    (eff : Effect) : g.support.Subset (Inference.Protected X g t eff) :=
  (Names.subset_union_left _ _).trans (Names.subset_union_left _ _)

theorem Inference.Protected.type {X : Constraints T O} (g : Context X) (t : T.Term)
    (eff : Effect) : (T.support t).Subset (Inference.Protected X g t eff) :=
  (Names.subset_union_right _ _).trans (Names.subset_union_left _ _)

theorem Inference.Protected.effect {X : Constraints T O} (g : Context X) (t : T.Term)
    (eff : Effect) : eff.vars ⊆ (Inference.Protected X g t eff).effects :=
  Finset.subset_union_right

theorem Inference.Protected.eval_effect {X : Constraints T O} {g : Context X} {t : T.Term}
    {eff : Effect} {v w : Valuation T.Value} {fixed : Names}
    (h : (Inference.Protected X g t eff).Subset fixed) (hw : w.AgreeOn v fixed) :
    eff.eval w.effects = eff.eval v.effects := by
  unfold Effect.eval
  congr 1
  exact Finset.biUnion_congr rfl (fun i hi => hw.2 i (h.2 (Protected.effect g t eff hi)))

theorem Inference.Protected.ground_transport {sig : Signature T} {X : Constraints T O}
    {g : Context X} {e : Expr} {t : T.Term} {eff : Effect}
    {v w : Valuation T.Value} {fixed : Names}
    (h : (Inference.Protected X g t eff).Subset fixed) (hw : w.AgreeOn v fixed)
    (ht : GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects)) :
    GroundTyping sig O (g.ground w) e (T.eval w t) (eff.eval w.effects) := by
  rw [Context.ground_support (hw.mono ((Protected.context g t eff).trans h)),
    T.eval_support w v t (hw.mono ((Protected.type g t eff).trans h)),
    Protected.eval_effect h hw]
  exact ht

/-- The structural completeness assertion for the fixed generating procedure.
Its actual output covers every ground typing and valuation.
`fixed` can also protect names needed by previously generated subexpressions. -/
def Inference.GroundComplete (sig : Signature T) (X : Constraints T O)
    (N : X.Simplifier) (e : Expr) : Prop :=
  ∀ (g : Context X) (t : T.Term) (eff : Effect) (fixed : Names),
    (Inference.Protected X g t eff).Subset fixed →
    (∃ v, GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects)) →
    ∃ d, generate sig X N e g t eff fixed = some d ∧
      Inference sig X N X.top g e t eff d ∧
      ∀ v, GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects) →
        ∃ w, w.AgreeOn v fixed ∧ X.holds d w

theorem Inference.groundComplete_var (sig : Signature T) (X : Constraints T O)
    (N : X.Simplifier) (i : Nat) (g : Context X) (t : T.Term) (eff : Effect)
    (fixed : Names) (hfixed : (Inference.Protected X g t eff).Subset fixed)
    {s : Scheme X} (found : g[i]? = some s) :
    ∃ d, generate sig X N (.var i) g t eff fixed = some d ∧
      Inference sig X N X.top g (.var i) t eff d ∧
      ∀ v, GroundTyping sig O (g.ground v) (.var i) (T.eval v t) (eff.eval v.effects) →
        ∃ w, w.AgreeOn v fixed ∧ X.holds d w := by
  let guarded := fixed.union (X.support X.top)
  have hf : fixed.Subset guarded := Names.subset_union_left _ _
  have hs := Context.member_support (List.mem_of_getElem? found)
  have hgs : g.support.Subset fixed :=
    (Names.subset_union_left _ _).trans ((Names.subset_union_left _ _).trans hfixed)
  have hts : (T.support t).Subset fixed :=
    (Names.subset_union_right _ _).trans ((Names.subset_union_left _ _).trans hfixed)
  obtain ⟨d, deq, hd, hcov⟩ := Inference.variable_complete (sig := sig) (N := N) found t eff guarded
    Finset.subset_union_right Finset.subset_union_right
    (hts.1.trans hf.1) (hts.2.trans hf.2)
    (fun _ hi => hf.2 (hfixed.2 (Finset.mem_union_right _ hi)))
    (fun j hj => hf.1 (hgs.1 (hs.1 (Scheme.freeType_mem_support hj))))
    (fun j hj => hf.2 (hgs.2 (hs.2 (Scheme.freeEffect_mem_support hj))))
  refine ⟨d, by simp [generate, found, deq, guarded], hd, ?_⟩
  intro v hv
  obtain ⟨⟨s', a, hs', ha, hat⟩, heff⟩ := hv.var_inv rfl
  have hlookup : (g.ground v)[i]? = some {u | s.GroundInstance v u} := by
    simp [Context.ground, List.getElem?_map, found]
  rw [hlookup, Option.some.injEq] at hs'
  subst s'
  obtain ⟨w, hw, hdw⟩ := hcov v ((X.holds_top v).mpr trivial)
    (Scheme.groundInstance_sub ha hat) heff
  exact ⟨w, hw.mono hf, hdw⟩

theorem Inference.groundComplete_variable (sig : Signature T) (X : Constraints T O)
    (N : X.Simplifier) (i : Nat) : Inference.GroundComplete sig X N (.var i) := by
  intro g t eff fixed hfixed hex
  cases found : g[i]? with
  | some s => exact Inference.groundComplete_var sig X N i g t eff fixed hfixed found
  | none =>
      obtain ⟨v, hv⟩ := hex
      obtain ⟨⟨s, a, hs, _, _⟩, _⟩ := hv.var_inv rfl
      simp [Context.ground, List.getElem?_map, found] at hs

theorem Inference.groundComplete_int (sig : Signature T) (X : Constraints T O)
    (N : X.Simplifier) (n : Int) : Inference.GroundComplete sig X N (.int n) := by
  intro g t eff fixed _ _
  refine ⟨_, rfl, .int n, ?_⟩
  intro v hv
  have h := hv.int_inv rfl
  refine ⟨v, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, (X.holds_checked _ _ _ _ _ _ v).mpr ?_⟩
  refine ⟨(X.holds_top v).mpr trivial, (X.holds_top v).mpr trivial, ?_, ?_⟩
  · simpa only [T.eval_literal] using h.1
  · rw [h.2]; rfl

theorem Inference.groundComplete_bool (sig : Signature T) (X : Constraints T O)
    (N : X.Simplifier) (b : Bool) : Inference.GroundComplete sig X N (.bool b) := by
  intro g t eff fixed _ _
  refine ⟨_, rfl, .bool b, ?_⟩
  intro v hv
  have h := hv.bool_inv rfl
  refine ⟨v, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, (X.holds_checked _ _ _ _ _ _ v).mpr ?_⟩
  refine ⟨(X.holds_top v).mpr trivial, (X.holds_top v).mpr trivial, ?_, ?_⟩
  · simpa only [T.eval_literal] using h.1
  · rw [h.2]; rfl

theorem Inference.groundComplete_lam {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {body : Expr} (ih : Inference.GroundComplete sig X N body) :
    Inference.GroundComplete sig X N (.lam body) := by
  intro g t eff fixed hfixed hex
  let p := fixed.shiftTypes 0
  let q := fixed.shiftTypes 1
  let m := fixed.shiftEffects 0
  let a := T.var p
  let b := T.var q
  let latent := Effect.var m
  let childContext : Context X := .mono a :: g
  let locals : Names := ⟨{p, q}, {m}⟩
  let childFixed := fixed.union ((Inference.Protected X childContext b latent).union locals)
  have hchild : (Inference.Protected X childContext b latent).Subset childFixed :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have houter : fixed.Subset childFixed := Names.subset_union_left _ _
  have hlocal : locals.Subset childFixed :=
    (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
  have hgfixed : g.support.Subset fixed := (Protected.context g t eff).trans hfixed
  have htFixed : (T.support t).Subset fixed := (Protected.type g t eff).trans hfixed
  let seed (v : Valuation T.Value) (a b : T.Value) (el : Finset Op) :=
    v.fresh fixed (fun i => if i = 0 then a else b) (fun _ => el)
  have hseed (v : Valuation T.Value) (a' b' : T.Value) (el : Finset Op) :
      (seed v a' b' el).AgreeOn v fixed := v.fresh_agree _ _ _
  have hseedTypeA (v : Valuation T.Value) (a' b' : T.Value) (el : Finset Op) :
      T.eval (seed v a' b' el) a = a' := by
    simp [a, p, seed, T.eval_var, Valuation.fresh_types]
  have hseedTypeB (v : Valuation T.Value) (a' b' : T.Value) (el : Finset Op) :
      T.eval (seed v a' b' el) b = b' := by
    simp [b, q, seed, T.eval_var, Valuation.fresh_types]
  have hseedEffect (v : Valuation T.Value) (a' b' : T.Value) (el : Finset Op) :
      latent.eval (seed v a' b' el).effects = el := by
    simp [latent, m, seed, Effect.eval, Effect.var, Valuation.fresh_effects]
  have hseedContext (v : Valuation T.Value) (a' b' : T.Value) (el : Finset Op) :
      childContext.ground (seed v a' b' el) = upper O a' :: g.ground v := by
    rw [show childContext = .mono a :: g from rfl, Context.ground_cons_mono,
      hseedTypeA, Context.ground_support ((hseed v a' b' el).mono hgfixed)]
  have bodyExists : ∃ v, GroundTyping sig O (childContext.ground v) body
      (T.eval v b) (latent.eval v.effects) := by
    obtain ⟨v, hv⟩ := hex
    obtain ⟨⟨a', b', el, hb, _⟩, _⟩ := hv.lam_inv rfl
    exact ⟨seed v a' b' el, by simpa only [hseedContext, hseedTypeB, hseedEffect] using hb⟩
  obtain ⟨d, run_d, hd, hcov⟩ := ih childContext b latent childFixed hchild bodyExists
  refine ⟨_, ?_, .lam hd, ?_⟩
  · change (generate sig X N body childContext b latent childFixed >>= _) = _
    rw [run_d]; rfl

  intro v hv
  obtain ⟨⟨a', b', el, hb, hle⟩, heff⟩ := hv.lam_inv rfl
  have hbody : GroundTyping sig O (childContext.ground (seed v a' b' el)) body
      (T.eval (seed v a' b' el) b) (latent.eval (seed v a' b' el).effects) := by
    simpa only [hseedContext, hseedTypeB, hseedEffect] using hb
  obtain ⟨w, hw, hdw⟩ := hcov (seed v a' b' el) hbody
  have hwfixed := (hw.mono houter).trans (hseed v a' b' el)
  have hevalA : T.eval w a = a' := by
    rw [show a = T.var p from rfl, T.eval_var,
      hw.1 p (hlocal.1 (by simp [locals])), ← T.eval_var _ _]
    exact hseedTypeA v a' b' el
  have hevalB : T.eval w b = b' := by
    rw [show b = T.var q from rfl, T.eval_var,
      hw.1 q (hlocal.1 (by simp [locals])), ← T.eval_var _ _]
    exact hseedTypeB v a' b' el
  have hevalE : latent.eval w.effects = el := by
    have hm := hw.2 m (hlocal.2 (by simp [locals]))
    simpa [latent, m, seed, Effect.eval, Effect.var, Valuation.fresh_effects] using hm
  refine ⟨w, hwfixed, ?_⟩
  apply (X.holds_conjunction _ w).mpr
  simp only [List.mem_cons, forall_eq_or_imp]
  refine ⟨(X.holds_top w).mpr trivial, hdw, (X.holds_le _ _ w).mpr ?_,
    (X.holds_effectEq _ _ w).mpr ?_, by simp⟩
  · rw [T.eval_arrow, hevalA, hevalB, hevalE, T.eval_support w v t (hwfixed.mono htFixed)]
    exact hle
  · rw [Protected.eval_effect hfixed hwfixed, heff]; rfl

theorem Inference.groundComplete_app {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {f x : Expr} (ihf : Inference.GroundComplete sig X N f)
    (ihx : Inference.GroundComplete sig X N x) :
    Inference.GroundComplete sig X N (.app f x) := by
  intro g t eff fixed hfixed hex
  let ft := T.var (fixed.shiftTypes 0)
  let xt := T.var (fixed.shiftTypes 1)
  let ef := Effect.var (fixed.shiftEffects 0)
  let ex := Effect.var (fixed.shiftEffects 1)
  let latent := Effect.var (fixed.shiftEffects 2)
  let bothFixed := fixed.union ((Protected X g ft ef).union
    ((Protected X g xt ex).union ⟨∅, latent.vars⟩))
  have hfun : (Protected X g ft ef).Subset bothFixed :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have harg : (Protected X g xt ex).Subset bothFixed :=
    (Names.subset_union_left _ _).trans
      ((Names.subset_union_right _ _).trans (Names.subset_union_right _ _))
  have houter : fixed.Subset bothFixed := Names.subset_union_left _ _
  have hlat : latent.vars ⊆ bothFixed.effects :=
    Finset.subset_union_right.trans (Finset.subset_union_right.trans Finset.subset_union_right)
  let seed (v : Valuation T.Value) (a : T.Value) (ef' ex' el : Finset Op) :=
    v.fresh fixed (fun i => if i = 0 then T.groundArrow a el (T.eval v t) else a)
      (fun i => if i = 0 then ef' else if i = 1 then ex' else el)
  have hseed (v : Valuation T.Value) (a : T.Value) (ef' ex' el : Finset Op) :
      (seed v a ef' ex' el).AgreeOn v fixed := v.fresh_agree _ _ _
  have hctx (v : Valuation T.Value) (a : T.Value) (ef' ex' el : Finset Op) :
      g.ground (seed v a ef' ex' el) = g.ground v :=
    Context.ground_support ((hseed v a ef' ex' el).mono ((Protected.context g t eff).trans hfixed))
  have hft (v : Valuation T.Value) (a : T.Value) (ef' ex' el : Finset Op) :
      T.eval (seed v a ef' ex' el) ft = T.groundArrow a el (T.eval v t) := by
    simp [ft, seed, T.eval_var, Valuation.fresh_types]
  have hxt (v : Valuation T.Value) (a : T.Value) (ef' ex' el : Finset Op) :
      T.eval (seed v a ef' ex' el) xt = a := by
    simp [xt, seed, T.eval_var, Valuation.fresh_types]
  have hef (v : Valuation T.Value) (a : T.Value) (ef' ex' el : Finset Op) :
      ef.eval (seed v a ef' ex' el).effects = ef' := by
    simp [ef, seed, Effect.eval, Effect.var, Valuation.fresh_effects]
  have hex' (v : Valuation T.Value) (a : T.Value) (ef' ex' el : Finset Op) :
      ex.eval (seed v a ef' ex' el).effects = ex' := by
    simp [ex, seed, Effect.eval, Effect.var, Valuation.fresh_effects]
  have hel (v : Valuation T.Value) (a : T.Value) (ef' ex' el : Finset Op) :
      latent.eval (seed v a ef' ex' el).effects = el := by
    simp [latent, seed, Effect.eval, Effect.var, Valuation.fresh_effects]
  have fExists : ∃ v, GroundTyping sig O (g.ground v) f (T.eval v ft) (ef.eval v.effects) := by
    obtain ⟨v, hv⟩ := hex
    obtain ⟨a, ef', ex', el, hf, _, _⟩ := hv.app_inv rfl
    exact ⟨seed v a ef' ex' el, by simpa only [hctx, hft, hef] using hf⟩
  obtain ⟨df, run_df, hdf, hcovf⟩ := ihf g ft ef bothFixed hfun fExists
  let argFixed := bothFixed.union (X.support df)
  have hboth : bothFixed.Subset argFixed := Names.subset_union_left _ _
  have xExists : ∃ v, GroundTyping sig O (g.ground v) x (T.eval v xt) (ex.eval v.effects) := by
    obtain ⟨v, hv⟩ := hex
    obtain ⟨a, ef', ex', el, hf, hx, _⟩ := hv.app_inv rfl
    have hfseed : GroundTyping sig O (g.ground (seed v a ef' ex' el)) f
        (T.eval (seed v a ef' ex' el) ft) (ef.eval (seed v a ef' ex' el).effects) := by
      simpa only [hctx, hft, hef] using hf
    have hxseed : GroundTyping sig O (g.ground (seed v a ef' ex' el)) x
        (T.eval (seed v a ef' ex' el) xt) (ex.eval (seed v a ef' ex' el).effects) := by
      simpa only [hctx, hxt, hex'] using hx
    obtain ⟨w, hw, _⟩ := hcovf _ hfseed
    exact ⟨w, Protected.ground_transport harg hw hxseed⟩
  obtain ⟨dx, run_dx, hdx, hcovx⟩ := ihx g xt ex argFixed (harg.trans hboth) xExists
  refine ⟨_, ?_, .app (latent := latent) hdf hdx, ?_⟩
  · change (generate sig X N f g ft ef bothFixed >>= fun df =>
      generate sig X N x g xt ex (bothFixed.union (X.support df)) >>= fun dx =>
      some (X.conjunction [X.top, df, dx, X.le ft (T.arrow xt latent t), X.effectEq (ef ∪ ex ∪ latent) eff])) = _
    rw [run_df]; change (generate sig X N x g xt ex argFixed >>= _) = _
    rw [run_dx]; rfl

  intro v hv
  obtain ⟨a, ef', ex', el, hf, hx, heff⟩ := hv.app_inv rfl
  have hfseed : GroundTyping sig O (g.ground (seed v a ef' ex' el)) f
      (T.eval (seed v a ef' ex' el) ft) (ef.eval (seed v a ef' ex' el).effects) := by
    simpa only [hctx, hft, hef] using hf
  have hxseed : GroundTyping sig O (g.ground (seed v a ef' ex' el)) x
      (T.eval (seed v a ef' ex' el) xt) (ex.eval (seed v a ef' ex' el).effects) := by
    simpa only [hctx, hxt, hex'] using hx
  obtain ⟨w₁, hw₁, hdfw⟩ := hcovf _ hfseed
  obtain ⟨w₂, hw₂, hdxw⟩ := hcovx w₁ (Protected.ground_transport harg hw₁ hxseed)
  have hwseed := (hw₂.mono hboth).trans hw₁
  have hwfixed := (hwseed.mono houter).trans (hseed v a ef' ex' el)
  have hdfw₂ := (X.holds_support df w₂ w₁
    (hw₂.mono (Names.subset_union_right _ _))).mpr hdfw
  have hwft : T.eval w₂ ft = T.groundArrow a el (T.eval v t) :=
    (T.eval_support w₂ _ ft (hwseed.mono ((Protected.type g ft ef).trans hfun))).trans (hft _ _ _ _ _)
  have hwxt : T.eval w₂ xt = a :=
    (T.eval_support w₂ _ xt (hwseed.mono ((Protected.type g xt ex).trans harg))).trans (hxt _ _ _ _ _)
  have hwef : ef.eval w₂.effects = ef' :=
    (Protected.eval_effect hfun hwseed).trans (hef _ _ _ _ _)
  have hwex : ex.eval w₂.effects = ex' :=
    (Protected.eval_effect harg hwseed).trans (hex' _ _ _ _ _)
  have hwel : latent.eval w₂.effects = el := by
    have he : latent.eval w₂.effects = latent.eval (seed v a ef' ex' el).effects := by
      unfold Effect.eval
      congr 1
      exact Finset.biUnion_congr rfl (fun i hi => hwseed.2 i (hlat hi))
    exact he.trans (hel _ _ _ _ _)
  refine ⟨w₂, hwfixed, (X.holds_conjunction _ w₂).mpr ?_⟩
  simp only [List.mem_cons, forall_eq_or_imp]
  refine ⟨(X.holds_top w₂).mpr trivial, hdfw₂, hdxw, (X.holds_le _ _ w₂).mpr ?_,
    (X.holds_effectEq _ _ w₂).mpr ?_, by simp⟩
  · rw [hwft, T.eval_arrow, hwxt, hwel,
      T.eval_support w₂ v t (hwfixed.mono ((Protected.type g t eff).trans hfixed))]
    exact O.refl _
  · rw [effect_eval_union, effect_eval_union, hwef, hwex, hwel,
      Protected.eval_effect hfixed hwfixed, heff]

theorem Scheme.generalize_support {X : Constraints T O} (g : Context X) (c : X.Formula)
    (t : T.Term) : (Scheme.generalize g c t).support.Subset g.support := by
  constructor <;> intro i hi <;>
    simp only [Scheme.generalize, Scheme.support, Context.generalizationNames,
      Names.diff, Names.union, Finset.mem_sdiff, not_and, not_not] at hi <;>
    exact hi.2 hi.1

theorem Scheme.generalize_covers {X : Constraints T O} (g : Context X) (c : X.Formula)
    (t : T.Term) {v w : Valuation T.Value} {u : T.Value}
    (hw : w.AgreeOn v g.support) (hc : X.holds c w) (ht : O.le (T.eval w t) u) :
    (Scheme.generalize g c t).GroundInstance v u := by
  apply Scheme.qualifiedInstance_of_free_agreement
  · intro i hi
    exact hw.1 i ((Scheme.generalize_support g c t).1 (Scheme.freeType_mem_support hi))
  · intro i hi
    exact hw.2 i ((Scheme.generalize_support g c t).2 (Scheme.freeEffect_mem_support hi))
  · exact hc
  · exact ht

theorem Inference.groundComplete_letVal {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {val body : Expr} (hv : Value val)
    (ihv : Inference.GroundComplete sig X N val)
    (ihb : Inference.GroundComplete sig X N body) :
    Inference.GroundComplete sig X N (.letE val body) := by
  intro g t eff fixed hfixed hex
  let a := T.var (fixed.shiftTypes 0)
  let valFixed := fixed.union (Protected X g a ∅)
  have hval : (Protected X g a ∅).Subset valFixed := Names.subset_union_right _ _
  have houter : fixed.Subset valFixed := Names.subset_union_left _ _
  have hgfixed := (Protected.context g t eff).trans hfixed
  let seed (v : Valuation T.Value) (u : T.Value) := v.fresh fixed (fun _ => u) (fun _ => ∅)
  have hseed (v : Valuation T.Value) (u : T.Value) : (seed v u).AgreeOn v fixed :=
    v.fresh_agree _ _ _
  have hseedType (v : Valuation T.Value) (u : T.Value) : T.eval (seed v u) a = u := by
    simp [a, seed, T.eval_var, Valuation.fresh_types]
  have hseedContext (v : Valuation T.Value) (u : T.Value) :
      g.ground (seed v u) = g.ground v := Context.ground_support ((hseed v u).mono hgfixed)
  have valExists : ∃ v, GroundTyping sig O (g.ground v) val (T.eval v a) ((∅ : Effect).eval v.effects) := by
    obtain ⟨v, hroot⟩ := hex
    obtain ⟨s, ⟨u, hu⟩, hval, _⟩ := hroot.letVal_inv rfl hv
    refine ⟨seed v u, ?_⟩
    rw [hseedContext, hseedType]
    exact hval u hu
  obtain ⟨dv, run_dv, hdv, hcovv⟩ := ihv g a ∅ valFixed hval valExists
  let scheme := Scheme.generalize g (N.run dv) a
  let bound := g.generalizationNames (N.run dv) a
  let projected := X.existsNames bound (N.run dv)
  let newContext : Context X := scheme :: g
  have generalized (v : Valuation T.Value) (u : T.Value)
      (htu : GroundTyping sig O (g.ground v) val u ∅) : scheme.GroundInstance v u := by
    have hseedVal : GroundTyping sig O (g.ground (seed v u)) val (T.eval (seed v u) a)
        ((∅ : Effect).eval (seed v u).effects) := by
      rw [hseedContext, hseedType]
      exact htu
    obtain ⟨w, hw, hdw⟩ := hcovv (seed v u) hseedVal
    have hwg := ((hw.mono houter).trans (hseed v u)).mono hgfixed
    apply Scheme.generalize_covers g (N.run dv) a hwg ((N.equivalent dv).2 w hdw)
    rw [T.eval_support w (seed v u) a (hw.mono ((Protected.type g a ∅).trans hval)), hseedType]
    exact O.refl _
  have adapt (v : Valuation T.Value)
      (hroot : GroundTyping sig O (g.ground v) (.letE val body) (T.eval v t) (eff.eval v.effects)) :
      X.holds projected v ∧ GroundTyping sig O (newContext.ground v) body
        (T.eval v t) (eff.eval v.effects) := by
    obtain ⟨s, hne, hval, hbody⟩ := hroot.letVal_inv rfl hv
    have hcover : s ⊆ {u | scheme.GroundInstance v u} := fun u hu => generalized v u (hval u hu)
    constructor
    · obtain ⟨u, hu⟩ := hne
      obtain ⟨w, hw, hd, _⟩ := hcover hu
      exact (X.holds_exists _ _ v).mpr ⟨w, hw, hd⟩
    · exact hbody.context_mono ((GroundContext.CoveredBy.refl (g.ground v)).cons hcover)
  let bodyFixed := fixed.union ((Protected X newContext t eff).union (X.support projected))
  have hbFixed : (Protected X newContext t eff).Subset bodyFixed :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have hprojected : (X.support projected).Subset bodyFixed :=
    (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
  have bodyExists : ∃ v, GroundTyping sig O (newContext.ground v) body
      (T.eval v t) (eff.eval v.effects) := by
    obtain ⟨v, hv⟩ := hex
    exact ⟨v, (adapt v hv).2⟩
  obtain ⟨db, run_db, hdb, hcovb⟩ := ihb newContext t eff bodyFixed hbFixed bodyExists
  refine ⟨_, ?_, .letVal hv (g.generalizationNames_avoids (N.run dv) a) hdv hdb, ?_⟩
  · rw [generate, ite_eq_left (Value.isValue_iff val |>.mpr hv)]
    change (generate sig X N val g a ∅ valFixed >>= _) = _
    rw [run_dv]; change (generate sig X N body newContext t eff bodyFixed >>= _) = _
    rw [run_db]; rfl

  intro v hroot
  obtain ⟨hp, hb⟩ := adapt v hroot
  obtain ⟨w, hw, hdw⟩ := hcovb v hb
  refine ⟨w, hw.mono (Names.subset_union_left _ _), (X.holds_conjunction _ w).mpr ?_⟩
  simp only [List.mem_cons, forall_eq_or_imp]
  exact ⟨(X.holds_top w).mpr trivial,
    (X.holds_support projected w v (hw.mono hprojected)).mpr hp, hdw, by simp⟩

theorem Inference.groundComplete_letMono {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {val body : Expr} (hv : ¬ Value val)
    (ihv : Inference.GroundComplete sig X N val)
    (ihb : Inference.GroundComplete sig X N body) :
    Inference.GroundComplete sig X N (.letE val body) := by
  intro g t eff fixed hfixed hex
  let a := T.var (fixed.shiftTypes 0)
  let ev := Effect.var (fixed.shiftEffects 0)
  let eb := Effect.var (fixed.shiftEffects 1)
  let bodyContext : Context X := .mono a :: g
  let bothFixed := fixed.union ((Protected X g a ev).union (Protected X bodyContext t eb))
  have hval : (Protected X g a ev).Subset bothFixed :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have hbody : (Protected X bodyContext t eb).Subset bothFixed :=
    (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
  have houter : fixed.Subset bothFixed := Names.subset_union_left _ _
  let seed (v : Valuation T.Value) (u : T.Value) (ev' eb' : Finset Op) :=
    v.fresh fixed (fun _ => u) (fun i => if i = 0 then ev' else eb')
  have hseed (v : Valuation T.Value) (u : T.Value) (ev' eb' : Finset Op) :
      (seed v u ev' eb').AgreeOn v fixed := v.fresh_agree _ _ _
  have hctx (v : Valuation T.Value) (u : T.Value) (ev' eb' : Finset Op) :
      g.ground (seed v u ev' eb') = g.ground v :=
    Context.ground_support ((hseed v u ev' eb').mono ((Protected.context g t eff).trans hfixed))
  have ha (v : Valuation T.Value) (u : T.Value) (ev' eb' : Finset Op) :
      T.eval (seed v u ev' eb') a = u := by
    simp [a, seed, T.eval_var, Valuation.fresh_types]
  have ht (v : Valuation T.Value) (u : T.Value) (ev' eb' : Finset Op) :
      T.eval (seed v u ev' eb') t = T.eval v t :=
    T.eval_support _ v t ((hseed v u ev' eb').mono ((Protected.type g t eff).trans hfixed))
  have hev (v : Valuation T.Value) (u : T.Value) (ev' eb' : Finset Op) :
      ev.eval (seed v u ev' eb').effects = ev' := by
    simp [ev, seed, Effect.eval, Effect.var, Valuation.fresh_effects]
  have heb (v : Valuation T.Value) (u : T.Value) (ev' eb' : Finset Op) :
      eb.eval (seed v u ev' eb').effects = eb' := by
    simp [eb, seed, Effect.eval, Effect.var, Valuation.fresh_effects]
  have hbctx (v : Valuation T.Value) (u : T.Value) (ev' eb' : Finset Op) :
      bodyContext.ground (seed v u ev' eb') = upper O u :: g.ground v := by
    rw [show bodyContext = .mono a :: g from rfl, Context.ground_cons_mono, ha, hctx]
  have valExists : ∃ v, GroundTyping sig O (g.ground v) val (T.eval v a) (ev.eval v.effects) := by
    obtain ⟨v, hroot⟩ := hex
    obtain ⟨u, ev', eb', hval, _, _⟩ := hroot.letMono_inv rfl hv
    exact ⟨seed v u ev' eb', by simpa only [hctx, ha, hev] using hval⟩
  obtain ⟨dv, run_dv, hdv, hcovv⟩ := ihv g a ev bothFixed hval valExists
  let bodyFixed := bothFixed.union (X.support dv)
  have hboth : bothFixed.Subset bodyFixed := Names.subset_union_left _ _
  have bodyExists : ∃ v, GroundTyping sig O (bodyContext.ground v) body
      (T.eval v t) (eb.eval v.effects) := by
    obtain ⟨v, hroot⟩ := hex
    obtain ⟨u, ev', eb', hv', hb', _⟩ := hroot.letMono_inv rfl hv
    have hvseed : GroundTyping sig O (g.ground (seed v u ev' eb')) val
        (T.eval (seed v u ev' eb') a) (ev.eval (seed v u ev' eb').effects) := by
      simpa only [hctx, ha, hev] using hv'
    have hbseed : GroundTyping sig O (bodyContext.ground (seed v u ev' eb')) body
        (T.eval (seed v u ev' eb') t) (eb.eval (seed v u ev' eb').effects) := by
      simpa only [hbctx, ht, heb] using hb'
    obtain ⟨w, hw, _⟩ := hcovv _ hvseed
    exact ⟨w, Protected.ground_transport hbody hw hbseed⟩
  obtain ⟨db, run_db, hdb, hcovb⟩ := ihb bodyContext t eb bodyFixed (hbody.trans hboth) bodyExists
  refine ⟨_, ?_, .letMono hv hdv hdb, ?_⟩
  · rw [generate, ite_eq_right (fun h => hv ((Value.isValue_iff val).mp h))]
    change (generate sig X N val g a ev bothFixed >>= _) = _
    rw [run_dv]; change (generate sig X N body bodyContext t eb bodyFixed >>= _) = _
    rw [run_db]; rfl

  intro v hroot
  obtain ⟨u, ev', eb', hv', hb', heff⟩ := hroot.letMono_inv rfl hv
  have hvseed : GroundTyping sig O (g.ground (seed v u ev' eb')) val
      (T.eval (seed v u ev' eb') a) (ev.eval (seed v u ev' eb').effects) := by
    simpa only [hctx, ha, hev] using hv'
  have hbseed : GroundTyping sig O (bodyContext.ground (seed v u ev' eb')) body
      (T.eval (seed v u ev' eb') t) (eb.eval (seed v u ev' eb').effects) := by
    simpa only [hbctx, ht, heb] using hb'
  obtain ⟨w₁, hw₁, hdvw⟩ := hcovv _ hvseed
  obtain ⟨w₂, hw₂, hdbw⟩ := hcovb w₁ (Protected.ground_transport hbody hw₁ hbseed)
  have hwseed := (hw₂.mono hboth).trans hw₁
  have hwfixed := (hwseed.mono houter).trans (hseed v u ev' eb')
  refine ⟨w₂, hwfixed, (X.holds_conjunction _ w₂).mpr ?_⟩
  simp only [List.mem_cons, forall_eq_or_imp]
  refine ⟨(X.holds_top w₂).mpr trivial,
    (X.holds_support dv w₂ w₁ (hw₂.mono (Names.subset_union_right _ _))).mpr hdvw,
    hdbw, (X.holds_effectEq _ _ w₂).mpr ?_, by simp⟩
  rw [effect_eval_union, Protected.eval_effect hval hwseed, Protected.eval_effect hbody hwseed,
    hev, heb, Protected.eval_effect hfixed hwfixed, heff]

theorem Inference.groundComplete_perform {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {op : Op} {arg : Expr} (ih : Inference.GroundComplete sig X N arg) :
    Inference.GroundComplete sig X N (.perform op arg) := by
  intro g t eff fixed hfixed hex
  obtain ⟨initial, hinitial⟩ := hex
  obtain ⟨raw, hs, hclosed, _⟩ := hinitial.perform_inv rfl
  let sub := Substitution.freshen T raw.bound fixed.shiftTypes fixed.shiftEffects
  let tin := sub.apply raw.input
  let tout := sub.apply raw.output
  let keep := fixed.union ((T.support tin).union (T.support tout))
  let ea := Effect.var (keep.shiftEffects 0)
  let argFixed := keep.union (Protected X g tin ea)
  have hinput : (T.support tin).Subset keep :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have houtput : (T.support tout).Subset keep :=
    (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
  have hkeep : keep.Subset argFixed := Names.subset_union_left _ _
  have harg : (Protected X g tin ea).Subset argFixed := Names.subset_union_right _ _
  have houter : fixed.Subset keep := Names.subset_union_left _ _
  let imageVal (v z : Valuation T.Value) :=
    v.assignImages z raw.bound fixed.shiftTypes fixed.shiftEffects
  have himage (v z : Valuation T.Value) : (imageVal v z).AgreeOn v fixed :=
    v.assignImages_agree z raw.bound _ _ fixed
      (fixed.shiftTypes_disjoint raw.bound) (fixed.shiftEffects_disjoint raw.bound)
  have hpull (v z : Valuation T.Value) : (sub.pullback (imageVal v z)).AgreeOn z raw.bound :=
    v.assignImages_pullback z raw.bound _ _
      fixed.shiftTypes_injective.injOn fixed.shiftEffects_injective.injOn
  have himageInput (v z : Valuation T.Value) : T.eval (imageVal v z) tin = T.eval z raw.input := by
    rw [show tin = sub.apply raw.input from rfl, sub.eval_apply]
    exact T.eval_support _ z raw.input ((hpull v z).mono
      ⟨Finset.subset_union_left.trans hclosed.1, Finset.subset_union_left.trans hclosed.2⟩)
  have himageOutput (v z : Valuation T.Value) : T.eval (imageVal v z) tout = T.eval z raw.output := by
    rw [show tout = sub.apply raw.output from rfl, sub.eval_apply]
    exact T.eval_support _ z raw.output ((hpull v z).mono
      ⟨Finset.subset_union_right.trans hclosed.1, Finset.subset_union_right.trans hclosed.2⟩)
  let seed (v z : Valuation T.Value) (ea' : Finset Op) :=
    (imageVal v z).fresh keep (fun _ => v.types 0) (fun _ => ea')
  have hseedKeep (v z : Valuation T.Value) (ea' : Finset Op) :
      (seed v z ea').AgreeOn (imageVal v z) keep := (imageVal v z).fresh_agree _ _ _
  have hseed (v z : Valuation T.Value) (ea' : Finset Op) :
      (seed v z ea').AgreeOn v fixed := ((hseedKeep v z ea').mono houter).trans (himage v z)
  have hctx (v z : Valuation T.Value) (ea' : Finset Op) :
      g.ground (seed v z ea') = g.ground v :=
    Context.ground_support ((hseed v z ea').mono ((Protected.context g t eff).trans hfixed))
  have htin (v z : Valuation T.Value) (ea' : Finset Op) :
      T.eval (seed v z ea') tin = T.eval z raw.input :=
    (T.eval_support _ _ tin ((hseedKeep v z ea').mono hinput)).trans (himageInput v z)
  have htout (v z : Valuation T.Value) (ea' : Finset Op) :
      T.eval (seed v z ea') tout = T.eval z raw.output :=
    (T.eval_support _ _ tout ((hseedKeep v z ea').mono houtput)).trans (himageOutput v z)
  have hea (v z : Valuation T.Value) (ea' : Finset Op) :
      ea.eval (seed v z ea').effects = ea' := by
    simp [ea, seed, Effect.eval, Effect.var, Valuation.fresh_effects]
  have inv (v : Valuation T.Value)
      (h : GroundTyping sig O (g.ground v) (.perform op arg) (T.eval v t) (eff.eval v.effects)) :
      ∃ z ea', GroundTyping sig O (g.ground v) arg (T.eval z raw.input) ea' ∧
        O.le (T.eval z raw.output) (T.eval v t) ∧ eff.eval v.effects = {op} ∪ ea' := by
    obtain ⟨raw', hs', _, z, ea', harg, hle, heff⟩ := h.perform_inv rfl
    have heq : raw = raw' := Option.some.inj (hs.symm.trans hs')
    subst raw'
    exact ⟨z, ea', harg, hle, heff⟩
  have argExists : ∃ v, GroundTyping sig O (g.ground v) arg (T.eval v tin) (ea.eval v.effects) := by
    obtain ⟨z, ea', harg, _, _⟩ := inv initial hinitial
    exact ⟨seed initial z ea', by simpa only [hctx, htin, hea] using harg⟩
  obtain ⟨d, run_d, hd, hcov⟩ := ih g tin ea argFixed harg argExists
  refine ⟨_, ?_, .perform sub hs hclosed (fun _ h => h) (fun _ h => h) hd, ?_⟩
  · rw [generate, hs]
    change (generate sig X N arg g tin ea argFixed >>= _) = _
    rw [run_d]; rfl

  intro v hv
  obtain ⟨z, ea', hargGround, hle, heff⟩ := inv v hv
  have hargseed : GroundTyping sig O (g.ground (seed v z ea')) arg
      (T.eval (seed v z ea') tin) (ea.eval (seed v z ea').effects) := by
    simpa only [hctx, htin, hea] using hargGround
  obtain ⟨w, hw, hdw⟩ := hcov _ hargseed
  have hwfixed := (hw.mono (houter.trans hkeep)).trans (hseed v z ea')
  refine ⟨w, hwfixed, (X.holds_checked _ _ _ _ _ _ w).mpr ?_⟩
  refine ⟨(X.holds_top w).mpr trivial,
    (X.holds_and _ _ w).mpr ⟨hdw, (X.holds_le _ _ w).mpr (O.refl _)⟩, ?_, ?_⟩
  · rw [T.eval_support w _ tout (hw.mono (houtput.trans hkeep)), htout,
      T.eval_support w v t (hwfixed.mono ((Protected.type g t eff).trans hfixed))]
    exact hle
  · rw [effect_eval_union, effect_eval_singleton, Protected.eval_effect harg hw, hea,
      Protected.eval_effect hfixed hwfixed, heff]

theorem Constraints.clause_avoids_witnesses (X : Constraints T O) (rigid witnesses : Names) (c : X.Formula) :
    X.Avoids (X.clause rigid witnesses c) witnesses := by
  apply X.avoids_of_transport
  intro v w hw hc
  apply (X.holds_clause _ _ _ w).mpr
  intro z hz
  obtain ⟨u, hu, hcu⟩ := (X.holds_clause _ _ _ v).mp hc
    (v.patch z rigid) (v.patch_agreeOutside z rigid)
  refine ⟨u, ⟨?_, ?_⟩, hcu⟩
  · intro i hi
    have hui := hu.1 i hi
    by_cases hr : i ∈ rigid.types
    · simpa [Valuation.patch, hr] using hui
    · simp only [Valuation.patch, hr, ↓reduceIte] at hui
      exact hui.trans ((hw.1 i hi).trans (hz.1 i hr).symm)
  · intro i hi
    have hui := hu.2 i hi
    by_cases hr : i ∈ rigid.effects
    · simpa [Valuation.patch, hr] using hui
    · simp only [Valuation.patch, hr, ↓reduceIte] at hui
      exact hui.trans ((hw.2 i hi).trans (hz.2 i hr).symm)

/-- Hide clause-local inference names inside the rigid operation quantifier.
The same generated constraint covers every rigid-parameter assignment. -/
theorem Inference.groundComplete_clause {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {clause : Expr} (ih : Inference.GroundComplete sig X N clause)
    (g : Context X) (t : T.Term) (out : Effect) (rigid fixed : Names)
    (hf : (Inference.Protected X g t out).Subset fixed)
    (hex : ∃ v e, GroundTyping sig O (g.ground v) clause (T.eval v t) e) :
    ∃ (eo : Effect) (dc : X.Formula) (hidden : Names), hidden.Disjoint fixed ∧
      eo = Effect.var (fixed.shiftEffects 0) ∧
      generate sig X N clause g t eo (fixed.union (Inference.Protected X g t eo)) = some dc ∧
      hidden = ((X.support dc).union ⟨∅, eo.vars⟩).diff fixed ∧
      Inference sig X N X.top g clause t eo dc ∧
      ∀ v, (∀ w, w.AgreeOutside v rigid → ∃ e,
        GroundTyping sig O (g.ground w) clause (T.eval w t) e ∧ e ⊆ out.eval w.effects) →
        X.holds (X.clause rigid hidden (X.and dc (X.and (X.le t t) (X.effectLe eo out)))) v := by
  let eo := Effect.var (fixed.shiftEffects 0)
  let childFixed := fixed.union (Inference.Protected X g t eo)
  have hfchild : fixed.Subset childFixed := Names.subset_union_left _ _
  have hchild : (Inference.Protected X g t eo).Subset childFixed := Names.subset_union_right _ _
  let seed (v : Valuation T.Value) (e : Finset Op) := v.fresh fixed v.types (fun _ => e)
  have hs (v : Valuation T.Value) (e : Finset Op) : (seed v e).AgreeOn v fixed :=
    v.fresh_agree _ _ _
  have hse (v : Valuation T.Value) (e : Finset Op) : eo.eval (seed v e).effects = e := by
    simp [eo, seed, Effect.eval, Effect.var, Valuation.fresh_effects]
  have hst (v : Valuation T.Value) (e : Finset Op) : T.eval (seed v e) t = T.eval v t :=
    T.eval_support _ _ _ ((hs v e).mono ((Protected.type g t out).trans hf))
  have hsg (v : Valuation T.Value) (e : Finset Op) : g.ground (seed v e) = g.ground v :=
    Context.ground_support ((hs v e).mono ((Protected.context g t out).trans hf))
  obtain ⟨dc, run_dc, hdc, hc⟩ := ih g t eo childFixed hchild (by
    obtain ⟨v, e, he⟩ := hex
    exact ⟨seed v e, by simpa only [hsg, hst, hse] using he⟩)
  let hidden := ((X.support dc).union ⟨∅, eo.vars⟩).diff fixed
  have hlocal : hidden.Disjoint fixed := by
    constructor <;> apply Finset.disjoint_left.mpr <;> intro i hi hf
    · exact (Finset.mem_sdiff.mp hi).2 hf
    · exact (Finset.mem_sdiff.mp hi).2 hf
  have hem : fixed.shiftEffects 0 ∈ hidden.effects := by
    have hn : fixed.shiftEffects 0 ∉ fixed.effects := by
      intro hm
      have := Finset.le_sup (f := id) hm
      simp only [Names.shiftEffects, Nat.add_zero, id_eq] at this
      omega
    simp [hidden, Names.diff, Names.union, eo, Effect.var, hn]
  refine ⟨eo, dc, hidden, hlocal, rfl, run_dc, rfl, hdc, ?_⟩
  intro v hv
  apply (X.holds_clause _ _ _ v).mpr
  intro w hw
  obtain ⟨e, he, hle⟩ := hv w hw
  obtain ⟨u, hu, hdu⟩ := hc (seed w e) (by simpa only [hsg, hst, hse] using he)
  have huf := (hu.mono hfchild).trans (hs w e)
  let z := w.patch u hidden
  have hz : z.AgreeOn w fixed := by
    constructor
    · intro i hi
      simp [z, Valuation.patch, show i ∉ hidden.types from
        fun hm => Finset.disjoint_left.mp hlocal.1 hm hi]
    · intro i hi
      simp [z, Valuation.patch, show i ∉ hidden.effects from
        fun hm => Finset.disjoint_left.mp hlocal.2 hm hi]
  have hzu : z.AgreeOn u (X.support dc) := by
    constructor
    · intro i hi
      by_cases hm : i ∈ hidden.types
      · simp [z, Valuation.patch, hm]
      · have hif : i ∈ fixed.types := by
          by_contra hn
          exact hm (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hi, hn⟩)
        simpa [z, Valuation.patch, hm] using (huf.1 i hif).symm
    · intro i hi
      by_cases hm : i ∈ hidden.effects
      · simp [z, Valuation.patch, hm]
      · have hif : i ∈ fixed.effects := by
          by_contra hn
          exact hm (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hi, hn⟩)
        simpa [z, Valuation.patch, hm] using (huf.2 i hif).symm
  have heo : eo.eval z.effects = e := by
    have heq := (Protected.eval_effect hchild hu).trans (hse w e)
    simpa [eo, Effect.eval, Effect.var, z, Valuation.patch, hem] using heq
  refine ⟨z, w.patch_agreeOutside u hidden, (X.holds_and _ _ z).mpr
    ⟨(X.holds_support dc z u hzu).mpr hdu, (X.holds_and _ _ z).mpr
      ⟨(X.holds_le _ _ z).mpr (O.refl _), (X.holds_effectLe _ _ z).mpr ?_⟩⟩⟩
  rw [heo, Protected.eval_effect hf hz]
  exact hle

theorem Inference.groundComplete_handle {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {body ret clause : Expr} {op : Op}
    (ihb : Inference.GroundComplete sig X N body)
    (ihr : Inference.GroundComplete sig X N ret)
    (ihc : Inference.GroundComplete sig X N clause) :
    Inference.GroundComplete sig X N (.handle body op ret clause) := by
  intro g target out fixed hf hex
  obtain ⟨v₀, hv₀⟩ := hex
  obtain ⟨raw, hs, hc, _⟩ := hv₀.handle_inv rfl
  let input := T.var (fixed.shiftTypes 0)
  let result := T.var (fixed.shiftTypes 1)
  let ein := Effect.var (fixed.shiftEffects 0)
  let er := Effect.var (fixed.shiftEffects 1)
  let rest := Effect.var (fixed.shiftEffects 2)
  let core := fixed.union ((T.support input).union ((T.support result).union
    ⟨∅, ein.vars ∪ er.vars ∪ rest.vars⟩))
  have hfixed : fixed.Subset core := Names.subset_union_left _ _
  have hi : (T.support input).Subset core :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have hr : (T.support result).Subset core :=
    (Names.subset_union_left _ _).trans ((Names.subset_union_right _ _).trans (Names.subset_union_right _ _))
  have hgs : g.support.Subset core := ((Protected.context g target out).trans hf).trans hfixed
  have hts : (T.support target).Subset core := ((Protected.type g target out).trans hf).trans hfixed
  have hes : ein.vars ∪ er.vars ∪ rest.vars ∪ out.vars ⊆ core.effects := by
    intro i hm
    simp only [Finset.mem_union] at hm
    rcases hm with ((hin | her) | hrest) | hout
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hin))))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_union_right _ her))))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_right _ hrest)))
    · exact hfixed.2 (hf.2 (Protected.effect g target out hout))
  let P (v : Valuation T.Value) : Prop :=
    GroundTyping sig O (g.ground v) body (T.eval v input) (ein.eval v.effects) ∧
    GroundTyping sig O (upper O (T.eval v input) :: g.ground v) ret
      (T.eval v result) (er.eval v.effects) ∧
    (∀ z : Valuation T.Value, ∃ eo,
      GroundTyping sig O
        (upper O (T.groundArrow (T.eval z raw.output) (out.eval v.effects) (T.eval v result)) ::
          upper O (T.eval z raw.input) :: g.ground v) clause (T.eval v result) eo ∧
      eo ⊆ out.eval v.effects) ∧
    rest.eval v.effects ⊆ ein.eval v.effects ∧
    ein.eval v.effects ⊆ {op} ∪ rest.eval v.effects ∧ op ∉ rest.eval v.effects ∧
    rest.eval v.effects ⊆ out.eval v.effects ∧ er.eval v.effects ⊆ out.eval v.effects ∧
    O.le (T.eval v result) (T.eval v target)
  have heval (v w : Valuation T.Value) (hw : w.AgreeOn v core) (eff : Effect)
      (he : eff.vars ⊆ core.effects) : eff.eval w.effects = eff.eval v.effects := by
    unfold Effect.eval
    congr 1
    exact Finset.biUnion_congr rfl (fun i hi => hw.2 i (he hi))
  have hein : ein.vars ⊆ core.effects :=
    (Finset.subset_union_left.trans Finset.subset_union_left).trans (Finset.subset_union_left.trans hes)
  have her : er.vars ⊆ core.effects :=
    (Finset.subset_union_right.trans Finset.subset_union_left).trans (Finset.subset_union_left.trans hes)
  have hrest : rest.vars ⊆ core.effects := Finset.subset_union_right.trans (Finset.subset_union_left.trans hes)
  have hout : out.vars ⊆ core.effects := Finset.subset_union_right.trans hes
  have transport {v w : Valuation T.Value} (hw : w.AgreeOn v core) (hp : P v) : P w := by
    simpa only [P, Context.ground_support (hw.mono hgs), T.eval_support w v input (hw.mono hi),
      T.eval_support w v result (hw.mono hr), T.eval_support w v target (hw.mono hts),
      heval v w hw ein hein, heval v w hw er her, heval v w hw rest hrest,
      heval v w hw out hout] using hp
  have seed (v : Valuation T.Value)
      (hv : GroundTyping sig O (g.ground v) (.handle body op ret clause)
        (T.eval v target) (out.eval v.effects)) : ∃ w, w.AgreeOn v fixed ∧ P w := by
    obtain ⟨raw', hs', _, a, b, ei, er', rest', hb, hr', hcl, h₁, h₂, h₃, h₄, h₅, hle⟩ := hv.handle_inv rfl
    rw [hs, Option.some.injEq] at hs'; subst raw'
    let w := v.fresh fixed (fun i => if i = 0 then a else b)
      (fun i => if i = 0 then ei else if i = 1 then er' else rest')
    have hw : w.AgreeOn v fixed := v.fresh_agree _ _ _
    refine ⟨w, hw, ?_⟩
    dsimp only [P]
    rw [Context.ground_support (hw.mono ((Protected.context g target out).trans hf)),
      T.eval_support w v target (hw.mono ((Protected.type g target out).trans hf)),
      Protected.eval_effect hf hw]
    simpa [input, result, ein, er, rest, w, T.eval_var, Effect.eval, Effect.var,
      Valuation.fresh_types, Valuation.fresh_effects] using
      And.intro hb (And.intro hr' (And.intro hcl (And.intro h₁ (And.intro h₂ (And.intro h₃ (And.intro h₄ (And.intro h₅ hle)))))))
  obtain ⟨start, _, hpstart⟩ := seed v₀ hv₀
  have hbprot : (Protected X g input ein).Subset core := by
    constructor <;> intro i hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · rcases Finset.mem_union.mp hm with hm | hm
        · exact hgs.1 hm
        · exact hi.1 hm
      · exact False.elim (Finset.notMem_empty _ hm)
    · rcases Finset.mem_union.mp hm with hm | hm
      · rcases Finset.mem_union.mp hm with hm | hm
        · exact hgs.2 hm
        · exact hi.2 hm
      · exact hein hm
  obtain ⟨db, run_db, hdb, covb⟩ := ihb g input ein core hbprot ⟨start, hpstart.1⟩
  let rf := core.union (X.support db)
  have hcr : core.Subset rf := Names.subset_union_left _ _
  have hrprot : (Protected X (.mono input :: g) result er).Subset rf := by
    constructor <;> intro i hm
    · simp only [Protected, Context.support, List.foldr_cons, Scheme.support,
        Names.union, Finset.mem_union, Finset.notMem_empty, or_false] at hm
      rcases hm with (hm | hm) | hm
      · exact hcr.1 (hi.1 hm)
      · exact hcr.1 (hgs.1 hm)
      · exact hcr.1 (hr.1 hm)
    · simp only [Protected, Context.support, List.foldr_cons, Scheme.support,
        Names.union, Finset.mem_union] at hm
      rcases hm with ((hm | hm) | hm) | hm
      · exact hcr.2 (hi.2 hm)
      · exact hcr.2 (hgs.2 hm)
      · exact hcr.2 (hr.2 hm)
      · exact hcr.2 (her hm)
  obtain ⟨dr, run_dr, hdr, covr⟩ := ihr (.mono input :: g) result er rf hrprot
    ⟨start, by simpa only [Context.ground_cons_mono] using hpstart.2.1⟩
  let outer := rf.union (X.support dr)
  have hro : rf.Subset outer := Names.subset_union_left _ _
  have hco := hcr.trans hro
  let decl := raw.rename outer.shiftTypes outer.shiftEffects
  have fresh : raw.FreshInstance decl :=
    ⟨_, _, outer.shiftTypes_injective.injOn, outer.shiftEffects_injective.injOn, rfl⟩
  have hrigid : decl.bound.Disjoint outer :=
    ⟨outer.shiftTypes_disjoint raw.bound, outer.shiftEffects_disjoint raw.bound⟩
  let cg : Context X := .mono (T.arrow decl.output out result) :: .mono decl.input :: g
  let cf := outer.union ((Protected X cg result out).union
    (((T.support decl.input).union (T.support decl.output)).union decl.bound))
  have hoc : outer.Subset cf := Names.subset_union_left _ _
  have hcp : (Protected X cg result out).Subset cf :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have clauseGround {v : Valuation T.Value} (hp : P v) (w : Valuation T.Value)
      (hw : w.AgreeOutside v decl.bound) : ∃ eo,
      GroundTyping sig O (cg.ground w) clause (T.eval w result) eo ∧ eo ⊆ out.eval w.effects := by
    have hwo : w.AgreeOn v outer :=
      ⟨fun i hi => hw.1 i (fun hm => Finset.disjoint_left.mp hrigid.1 hm hi),
        fun i hi => hw.2 i (fun hm => Finset.disjoint_left.mp hrigid.2 hm hi)⟩
    have hpw := transport (hwo.mono hco) hp
    obtain ⟨eo, heo, hle⟩ := hpw.2.2.1 ⟨w.types ∘ outer.shiftTypes, w.effects ∘ outer.shiftEffects⟩
    refine ⟨eo, ?_, hle⟩
    simpa only [cg, Context.ground_cons_mono, T.eval_arrow, decl, Operation.rename,
      T.eval_rename] using heo
  obtain ⟨eo, dc, hidden, hhidden, eo_eq, run_dc, hidden_eq, hdc, covc⟩ := Inference.groundComplete_clause ihc cg result out decl.bound cf hcp (by
    obtain ⟨e, he, _⟩ := clauseGround hpstart start ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    exact ⟨start, e, he⟩)
  let cq := X.clause decl.bound hidden (X.and dc (X.and (X.le result result) (X.effectLe eo out)))
  let d := X.handler X.top db dr dc decl op result result result ein er eo rest out hidden
  have shape (v : Valuation T.Value) : X.holds d v ↔
      X.holds db v ∧ X.holds dr v ∧ X.holds cq v ∧
      rest.eval v.effects ⊆ ein.eval v.effects ∧
      ein.eval v.effects ⊆ {op} ∪ rest.eval v.effects ∧ op ∉ rest.eval v.effects ∧
      rest.eval v.effects ⊆ out.eval v.effects ∧ er.eval v.effects ⊆ out.eval v.effects := by
    simp [d, Constraints.handler, X.holds_conjunction, X.holds_top, X.holds_le, O.refl,
      Constraints.split, X.holds_and, X.holds_effectLe, X.holds_lacks,
      effect_eval_union, effect_eval_singleton, cq, and_assoc]
  have hdbs : (X.support db).Subset outer := (Names.subset_union_right _ _).trans hro
  have hdrs : (X.support dr).Subset outer := Names.subset_union_right _ _
  have avoid : X.Avoids d hidden := by
    apply X.avoids_of_transport
    intro v w hw hv
    have hwo : w.AgreeOn v outer :=
      ⟨fun i hi => (hw.1 i (fun hm => Finset.disjoint_left.mp hhidden.1 hm (hoc.1 hi))).symm,
        fun i hi => (hw.2 i (fun hm => Finset.disjoint_left.mp hhidden.2 hm (hoc.2 hi))).symm⟩
    obtain ⟨hb, hr', hcl, he⟩ := (shape v).mp hv
    apply (shape w).mpr
    refine ⟨(X.holds_support db w v (hwo.mono hdbs)).mpr hb,
      (X.holds_support dr w v (hwo.mono hdrs)).mpr hr',
      (X.holds_agreeOutside (X.clause_avoids_witnesses decl.bound hidden _) hw).mp hcl, ?_⟩
    simpa only [heval v w (hwo.mono hco) ein hein, heval v w (hwo.mono hco) er her,
      heval v w (hwo.mono hco) rest hrest, heval v w (hwo.mono hco) out hout] using he
  have hscope : decl.Scoped X d g input result ein er rest out hidden := by
    constructor
    · exact g.avoids_of_support_disjoint decl.bound (hrigid.mono_right (hgs.trans hco))
    · exact hrigid.mono_right ((hi.union hr).trans hco)
    · exact Finset.disjoint_left.mpr fun i hm he =>
        Finset.disjoint_left.mp hrigid.2 hm (hco.2 (hes he))
    · have hdecl : (((T.support decl.input).union (T.support decl.output)).union decl.bound).Subset cf :=
        (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
      exact hhidden.mono_right (((hgs.trans hco).trans hoc).union
        ((((hi.union hr).trans hco).trans hoc).union hdecl))
    · exact avoid
    · exact Finset.disjoint_left.mpr fun i hm he =>
        Finset.disjoint_left.mp hhidden.2 hm (hoc.2 (hco.2 (hes he)))
  have generated : Inference sig X N X.top g (.handle body op ret clause) result out d :=
    .handle hs hc fresh hscope hdb hdr hdc
  refine ⟨_, ?_, .check generated, ?_⟩
  · rw [generate, hs]
    change (generate sig X N body g input ein core >>= _) = _
    rw [run_db]; change (generate sig X N ret (.mono input :: g) result er rf >>= _) = _
    rw [run_dr]
    change (generate sig X N clause cg result (Effect.var (cf.shiftEffects 0))
      (cf.union (Protected X cg result (Effect.var (cf.shiftEffects 0)))) >>= _) = _
    rw [← eo_eq, run_dc]
    change some (X.checked X.top (X.handler X.top db dr dc decl op result result result
      ein er eo rest out (((X.support dc).union ⟨∅, eo.vars⟩).diff cf)) result target out out) = _
    rw [← hidden_eq]

  intro v hv
  obtain ⟨s, hsv, hps⟩ := seed v hv
  obtain ⟨w₁, hw₁, hdb₁⟩ := covb s hps.1
  have hp₁ := transport hw₁ hps
  obtain ⟨w₂, hw₂, hdr₂⟩ := covr w₁ (by
    simpa only [Context.ground_cons_mono] using hp₁.2.1)
  have hp₂ := transport (hw₂.mono hcr) hp₁
  have hwfixed := (((hw₂.mono hcr).trans hw₁).mono hfixed).trans hsv
  refine ⟨w₂, hwfixed, (X.holds_checked _ _ _ _ _ _ w₂).mpr
    ⟨(X.holds_top w₂).mpr trivial, ?_, hp₂.2.2.2.2.2.2.2.2, rfl⟩⟩
  exact (shape w₂).mpr
    ⟨(X.holds_support db w₂ w₁ (hw₂.mono (Names.subset_union_right _ _))).mpr hdb₁,
      hdr₂, covc w₂ (clauseGround hp₂), hp₂.2.2.2.1, hp₂.2.2.2.2.1,
      hp₂.2.2.2.2.2.1, hp₂.2.2.2.2.2.2.1, hp₂.2.2.2.2.2.2.2.1⟩

/-- Completeness for the full language, including polymorphic value-let and
handlers, over the abstract type algebra and comparison order. -/
theorem Inference.groundComplete (sig : Signature T) (X : Constraints T O)
    (N : X.Simplifier) (e : Expr) : Inference.GroundComplete sig X N e := by
  classical
  induction e with
  | var i => exact groundComplete_variable sig X N i
  | int n => exact groundComplete_int sig X N n
  | bool b => exact groundComplete_bool sig X N b
  | lam body ih => exact groundComplete_lam ih
  | app f x ihf ihx => exact groundComplete_app ihf ihx
  | letE val body ihv ihb =>
      by_cases hv : Value val
      · exact groundComplete_letVal hv ihv ihb
      · exact groundComplete_letMono hv ihv ihb
  | perform op arg ih => exact groundComplete_perform ih
  | handle body op ret clause ihb ihr ihc => exact groundComplete_handle ihb ihr ihc

end EHMX.HMX
